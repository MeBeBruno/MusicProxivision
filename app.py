import os
import re
import time
import json
import random
import hashlib
import uuid
import threading
from typing import Dict, List, Optional, Tuple

from flask import Flask, session, redirect, request, url_for, Response, render_template
from flask_session import Session
from dotenv import load_dotenv

import spotipy
from spotipy.oauth2 import SpotifyOAuth
from pytube import Search

import requests
from urllib.parse import urlparse, parse_qs

# -------------------------
# Bootstrap
# -------------------------
load_dotenv()

app = Flask(__name__)
app.secret_key = os.environ.get("FLASK_SECRET_KEY", "dev-change-me")

app.config["SESSION_TYPE"] = "filesystem"
app.config["SESSION_FILE_DIR"] = os.environ.get("SESSION_FILE_DIR", "./.flask_session")
app.config["SESSION_PERMANENT"] = False
os.makedirs(app.config["SESSION_FILE_DIR"], exist_ok=True)
Session(app)

PORT = int(os.environ.get("PORT", "80"))
BASE_URL = os.environ.get("BASE_URL", "http://127.0.0.1:80").rstrip("/")
SPOTIFY_CLIENT_ID = os.environ.get("SPOTIFY_CLIENT_ID")
SPOTIFY_CLIENT_SECRET = os.environ.get("SPOTIFY_CLIENT_SECRET")
SPOTIFY_REDIRECT_PATH = os.environ.get("SPOTIFY_REDIRECT_PATH", "/spotify/callback")

# -------------------------
# In-Memory Job Store (pro Prozess)
# -------------------------
JOBS: Dict[str, Dict[str, dict]] = {}  # {uid: {job_id: {...}}}
JOBS_LOCK = threading.Lock()

def _get_uid() -> str:
    if "uid" not in session:
        session["uid"] = uuid.uuid4().hex
    return session["uid"]

def _fmt_seconds(secs: Optional[float]) -> Optional[str]:
    if secs is None:
        return None
    s = int(max(0, round(secs)))
    h, r = divmod(s, 3600)
    m, s = divmod(r, 60)
    return f"{h:d}:{m:02d}:{s:02d}" if h else f"{m:d}:{s:02d}"

def _job_init(uid: str) -> str:
    job_id = uuid.uuid4().hex
    with JOBS_LOCK:
        JOBS.setdefault(uid, {})
        JOBS[uid][job_id] = {
            "status": "queued",         # queued|running|resolving|done|error
            "message": "Warte auf Start",
            "total": 0,
            "done": 0,
            "percent": 0,
            "current": None,
            "links": [],               # watch_videos Links
            "playlist_links": [],      # echte /playlist?list=... Links (same length; None bis aufgelöst)
            "misses": [],
            "searches": [],
            "error": None,
            # ETA
            "started_at": None,
            "elapsed_seconds": 0,
            "eta_seconds": None,
            "eta_human": None,
            # Resolver-Progress
            "resolving_total": 0,
            "resolving_done": 0,
        }
    return job_id

def _job_update(uid: str, job_id: str, **kwargs):
    with JOBS_LOCK:
        job = JOBS.get(uid, {}).get(job_id)
        if not job:
            return
        job.update(kwargs)
        # Prozent (für Track-Scraping)
        if job["total"] > 0:
            job["percent"] = int(round(100 * job["done"] / job["total"]))
        # ETA / Elapsed
        now = time.time()
        if job.get("started_at"):
            elapsed = now - job["started_at"]
            job["elapsed_seconds"] = int(elapsed)
            if job["done"] > 0 and job["total"] > 0:
                per_item = elapsed / job["done"]
                remaining = max(job["total"] - job["done"], 0)
                eta = per_item * remaining
                job["eta_seconds"] = int(eta)
                job["eta_human"] = _fmt_seconds(eta)
            else:
                job["eta_seconds"] = None
                job["eta_human"] = None

def _job_get(uid: str, job_id: str) -> Optional[dict]:
    with JOBS_LOCK:
        return (JOBS.get(uid, {}) or {}).get(job_id)

# -------------------------
# Spotify / pytube Helpers
# -------------------------
def _spotify_oauth() -> SpotifyOAuth:
    return SpotifyOAuth(
        client_id=SPOTIFY_CLIENT_ID,
        client_secret=SPOTIFY_CLIENT_SECRET,
        redirect_uri=f"{BASE_URL}{SPOTIFY_REDIRECT_PATH}",
        scope="playlist-read-private playlist-read-collaborative",
        cache_path=None,
        show_dialog=False,
    )

def _spotify_client_from_token(token_info: Dict) -> spotipy.Spotify:
    """
    Erzeuge einen Spotipy-Client aus token_info (thread-safe; kein session-Zugriff).
    """
    local = dict(token_info)
    if local.get("expires_at") and local["expires_at"] - int(time.time()) < 60:
        oauth = _spotify_oauth()
        local = oauth.refresh_access_token(local["refresh_token"])
    return spotipy.Spotify(auth=local["access_token"])

_SPOTIFY_PL_REGEXES = [
    r"spotify:playlist:([A-Za-z0-9]+)",
    r"open\.spotify\.com/playlist/([A-Za-z0-9]+)",
    r"playlist\?list=([A-Za-z0-9]+)",
]

def extract_spotify_playlist_id(text: str) -> str:
    text = text.strip()
    for pat in _SPOTIFY_PL_REGEXES:
        m = re.search(pat, text)
        if m:
            return m.group(1)
    return text

def fetch_spotify_tracks(sp: spotipy.Spotify, playlist_id: str) -> List[Tuple[str, str]]:
    items: List[Tuple[str, str]] = []
    fields = "items(track(name,artists(name))),next"
    limit = 100
    results = sp.playlist_items(playlist_id, fields=fields, limit=limit)
    while True:
        for it in results.get("items", []):
            tr = it.get("track") or {}
            name = tr.get("name") or ""
            artists = tr.get("artists") or []
            primary_artist = artists[0]["name"] if artists else ""
            if name and primary_artist:
                items.append((name, primary_artist))
        if not results.get("next"):
            break
        results = sp.next(results)
    return items

def yt_search_first_id(query: str) -> Optional[str]:
    s = Search(query)
    res = s.results  # force load
    if not res:
        return None
    return getattr(res[0], "video_id", None)

def chunk(lst: List[str], n: int) -> List[List[str]]:
    return [lst[i:i+n] for i in range(0, len(lst), n)]

# -------------------------
# Resolve watch_videos -> playlist?list=...
# -------------------------
_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"

def resolve_watch_videos_to_playlist(url: str, timeout: int = 15) -> Optional[str]:
    """
    Ruft den watch_videos-Link auf, folgt Redirects und extrahiert eine 'list=' ID
    entweder aus der finalen URL oder aus dem HTML. Gibt /playlist?list=… URL zurück
    oder None, wenn nicht ermittelbar.
    """
    try:
        resp = requests.get(url, headers={"User-Agent": _UA}, allow_redirects=True, timeout=timeout)
        final_url = resp.url or url
        # 1) final URL prüfen
        parsed = urlparse(final_url)
        qs = parse_qs(parsed.query)
        list_id = qs.get("list", [None])[0]
        if not list_id:
            # 2) regex in final URL
            m = re.search(r"[?&]list=([A-Za-z0-9_-]+)", final_url)
            if m:
                list_id = m.group(1)
        if not list_id and resp.text:
            # 3) Fallback: HTML durchsuchen (canonical etc.)
            m = re.search(r"[?&]list=([A-Za-z0-9_-]+)", resp.text)
            if m:
                list_id = m.group(1)
        if list_id:
            return f"https://www.youtube.com/playlist?list={list_id}"
    except Exception:
        pass
    return None

def _resolve_links_worker(uid: str, job_id: str):
    # löst nacheinander alle watch_videos-Links in echte Playlist-URLs auf
    job = _job_get(uid, job_id)
    if not job:
        return
    links = job.get("links", [])
    total = len(links)
    for i, wv in enumerate(links, start=1):
        pl = resolve_watch_videos_to_playlist(wv)
        # aktuelle Liste holen & aktualisieren
        current = _job_get(uid, job_id)
        if not current:
            break
        pl_list = list(current.get("playlist_links", []) or [None] * total)
        if i - 1 < len(pl_list):
            pl_list[i - 1] = pl
        _job_update(
            uid, job_id,
            playlist_links=pl_list,
            resolving_total=total,
            resolving_done=i,
            message=f"Erzeuge Playlist-Links ({i}/{total}) …"
        )
        time.sleep(0.2)  # etwas höflich sein
    _job_update(uid, job_id, status="done", message="Fertig.")

# -------------------------
# Background Worker
# -------------------------
def _run_conversion(uid: str, job_id: str, playlist_input: str, suffix: str, token_info: Dict, shuffle_enabled: bool):
    try:
        _job_update(uid, job_id, status="running", message="Verbinde mit Spotify …", started_at=time.time())
        sp = _spotify_client_from_token(token_info)
        if sp is None:
            _job_update(uid, job_id, status="error", error="Spotify nicht verbunden.")
            return

        playlist_id = extract_spotify_playlist_id(playlist_input)
        tracks = fetch_spotify_tracks(sp, playlist_id)

        # ✅ Shuffle direkt NACH Spotify
        if shuffle_enabled and len(tracks) > 1:
            # stabil pro Job (nice zum Debuggen). Wenn du jedes Mal random willst: seed = time.time_ns()
            seed = int(hashlib.sha256(job_id.encode("utf-8")).hexdigest()[:8], 16)
            rng = random.Random(seed)
            rng.shuffle(tracks)

        total = len(tracks)
        _job_update(uid, job_id, total=total, done=0, message=f"{total} Tracks gefunden." + (" (Shuffle ✅)" if shuffle_enabled else ""))

        video_ids: List[str] = []
        misses: List[str] = []
        searches: List[str] = []

        for i, (title, artist) in enumerate(tracks, start=1):
            q = f"{title} - {artist} {suffix}".strip()
            searches.append(q)
            _job_update(uid, job_id, current=f"„{title}“ – {artist}", message="Suche auf YouTube …")
            try:
                vid = yt_search_first_id(q)
                if vid:
                    video_ids.append(vid)
                else:
                    misses.append(f"„{title}“ – {artist}")
            except Exception:
                misses.append(f"„{title}“ – {artist}")
            _job_update(uid, job_id, done=i)

        # Cleanup IDs + Links
        clean_ids, seen = [], set()
        for vid in video_ids:
            if vid and re.fullmatch(r"[A-Za-z0-9_-]{6,}", vid) and vid not in seen:
                seen.add(vid)
                clean_ids.append(vid)

        CHUNK = 45
        chunks = chunk(clean_ids, CHUNK)
        links = [
            "https://www.youtube.com/watch_videos?video_ids=" + ",".join(c)
            for c in chunks
        ]

        # Phase 1 fertig → Phase 2 (Resolve) starten
        _job_update(
            uid, job_id,
            status="resolving",
            message=f"Erzeuge Playlist-Links (0/{len(links)}) …",
            links=links,
            playlist_links=[None] * len(links),
            misses=misses,
            searches=searches,
            current=None
        )

        # separaten Worker für Link-Auflösung starten
        t2 = threading.Thread(target=_resolve_links_worker, args=(uid, job_id), daemon=True)
        t2.start()

    except Exception as e:
        _job_update(uid, job_id, status="error", error=str(e), message="Abgebrochen wegen Fehler.")

# -------------------------
# Routes
# -------------------------
@app.route("/")
def index():
    sp_ok = session.get("spotify_token") is not None
    return render_template(
        "index.html",
        sp_ok=sp_ok,
        base_url=BASE_URL,
        spotify_redirect_path=SPOTIFY_REDIRECT_PATH
    )

# ---- Spotify OAuth ----
@app.route("/spotify/login")
def spotify_login():
    if not SPOTIFY_CLIENT_ID or not SPOTIFY_CLIENT_SECRET:
        return "Spotify ENV Variablen fehlen (SPOTIFY_CLIENT_ID / SPOTIFY_CLIENT_SECRET).", 500
    oauth = _spotify_oauth()
    return redirect(oauth.get_authorize_url())

@app.route(SPOTIFY_REDIRECT_PATH)
def spotify_callback():
    error = request.args.get("error")
    if error:
        return f"Spotify OAuth Fehler: {error}", 400
    code = request.args.get("code")
    oauth = _spotify_oauth()
    token_info = oauth.get_access_token(code)
    session["spotify_token"] = token_info
    return redirect(url_for("index"))

# ---- API: Start + SSE Stream ----
@app.route("/api/start_convert", methods=["POST"])
def api_start_convert():
    token_info = session.get("spotify_token")
    if not token_info:
        return ("Spotify nicht verbunden.", 401)

    playlist_input = request.form.get("spotify_playlist", "").strip()
    suffix = (request.form.get("search_suffix", "Official Music Video HD") or "Official Music Video HD").strip()

    # ✅ Checkbox (wenn aus: fehlt komplett)
    shuffle_enabled = request.form.get("shuffle") in ("1", "on", "true", "yes")

    if not playlist_input:
        return ("Fehlende Eingaben.", 400)

    uid = _get_uid()
    job_id = _job_init(uid)

    t = threading.Thread(
        target=_run_conversion,
        args=(uid, job_id, playlist_input, suffix, dict(token_info), shuffle_enabled),
        daemon=True
    )
    t.start()
    return {"job_id": job_id}

@app.route("/api/stream/<job_id>")
def api_stream(job_id: str):
    uid = _get_uid()

    def gen():
        last_snapshot = None
        while True:
            job = _job_get(uid, job_id)
            if not job:
                data = {"status": "error", "error": "Job unbekannt"}
                yield f"data: {json.dumps(data, ensure_ascii=False)}\n\n"
                break
            snap = (
                job.get("status"), job.get("done"), job.get("total"),
                job.get("message"), job.get("current"),
                job.get("resolving_done"), job.get("resolving_total")
            )
            if snap != last_snapshot:
                last_snapshot = snap
                yield f"data: {json.dumps(job, ensure_ascii=False)}\n\n"
            if job.get("status") in ("done", "error"):
                break
            time.sleep(0.35)

    headers = {
        "Cache-Control": "no-cache",
        "X-Accel-Buffering": "no",  # nginx/traefik: buffering aus
    }
    return Response(gen(), mimetype="text/event-stream", headers=headers)

# -------------------------
# Run
# -------------------------
if __name__ == "__main__":
    app.run(host="0.0.0.0", port=PORT, threaded=True)
