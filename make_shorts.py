#!/usr/bin/env python3
"""
Urdu YouTube Shorts maker  -  version 2

Reads scripts.txt and makes one vertical 1080x1920 MP4 per script (in ./out).
  - Voice:      Microsoft neural voice ur-PK-AsadNeural (male Urdu, free, needs internet)
  - Footage:    stock clips from Pixabay (if PIXABAY_API_KEY is set) or from your own
                "clips" folder; if there is none, a moving gradient is used instead
  - Graphics:   Urdu captions (Nastaliq), emoji icons, big-number cards, simple bar charts
  - Editing:    a new background clip + whoosh sound at every line, pop-in captions,
                optional background music from the "music" folder

scripts.txt format - see the example file. In short:
    Title line (Urdu)
    search: english words for stock footage      (optional)
    [emoji:🧠] a line of narration               (tags are optional, see below)
    [stat:24/7] another line
    [bar:الف=70|ب=40] another line
    tags: #Shorts #اردو                          (optional)
    ---                                          (separates videos)

Tags that can start a narration line (several can be combined):
    [emoji:🧠]      big icon above the caption (use ONE simple emoji)
    [stat:70%]      big number / short text card above the caption
    [bar:label=70|label=40]   simple bar chart (values 0-100)
    [search:robot]  English words used to find footage for this line
    [pause:0.6]     extra pause (seconds) after this line
    [rate:+8%]      speak this line faster (+) or slower (-)
"""
import argparse
import array
import asyncio
import glob
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.parse
import urllib.request
import wave
from pathlib import Path

from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps, features

HERE = Path(__file__).resolve().parent

W, H, FPS = 1080, 1920, 30
VOICE = os.environ.get("TTS_VOICE", "ur-PK-AsadNeural")   # male Urdu (Pakistan)
RATE = os.environ.get("TTS_RATE", "+0%").strip() or "+0%"  # "+10%" faster, "-10%" slower
PITCH = os.environ.get("TTS_PITCH", "").strip()            # e.g. "-3Hz" (optional)
PIXABAY_KEY = os.environ.get("PIXABAY_API_KEY", "").strip()
SFX = os.environ.get("SFX", "1") != "0"                     # whoosh at every cut
MUSIC_VOLUME = float(os.environ.get("MUSIC_VOLUME", "0.12") or 0.12)

LEAD, GAP, TAIL = 0.35, 0.30, 0.80   # seconds: before first line, between lines, after last
LANG = "ur"
SAMPLE_RATE = 44100
VIDEO_EXT = {".mp4", ".mov", ".webm", ".mkv", ".m4v"}
MUSIC_EXT = {".mp3", ".wav", ".m4a", ".ogg", ".aac"}

# (top colour, bottom colour, accent colour) - cycles per video
PALETTES = [
    ((14, 36, 84), (88, 28, 135), (255, 196, 61)),
    ((6, 78, 59), (6, 30, 50), (253, 224, 71)),
    ((127, 29, 29), (30, 20, 60), (251, 146, 60)),
    ((8, 47, 73), (19, 78, 74), (125, 211, 252)),
    ((49, 46, 129), (136, 19, 55), (253, 164, 175)),
]


def warn(msg):
    print(f"  ! {msg}")


# --------------------------------------------------------------------------- #
# Reading scripts
# --------------------------------------------------------------------------- #
def parse_line(raw):
    """Split leading [key:value] tags from the narration text."""
    tags, text = {}, raw
    while True:
        m = re.match(r"\s*\[([A-Za-z]+)\s*:\s*([^\]]*)\]\s*", text)
        if not m:
            break
        tags[m.group(1).lower()] = m.group(2).strip()
        text = text[m.end():]
    return text.strip(), tags


def parse_scripts(text):
    videos = []
    for chunk in re.split(r"^\s*---+\s*$", text, flags=re.M):
        lines = [l.strip() for l in chunk.splitlines()]
        lines = [l for l in lines if l and not l.startswith("#")]
        if len(lines) < 2:
            continue
        title, tags, search, narration = lines[0], "", "", []
        for l in lines[1:]:
            low = l.lower()
            if low.startswith("tags:"):
                tags = l[5:].strip()
            elif low.startswith("search:"):
                search = l[7:].strip()
            else:
                t, tg = parse_line(l)
                if t:
                    narration.append({"text": t, "tags": tg})
        if narration:
            videos.append({"title": title, "lines": narration, "tags": tags, "search": search})
    return videos


# --------------------------------------------------------------------------- #
# Fonts and text drawing (Pillow + libraqm does the Urdu shaping / right-to-left)
# --------------------------------------------------------------------------- #
def _glob_fonts(pattern_name):
    out = []
    for root in ("/usr/share/fonts", "/usr/local/share/fonts", str(Path.home() / ".fonts")):
        out += [f for f in glob.glob(f"{root}/**/*{pattern_name}*", recursive=True)
                if f.lower().endswith((".ttf", ".otf"))]
    return sorted(out)


def _pick(files):
    bold = [f for f in files if "bold" in Path(f).name.lower() and "semi" not in Path(f).name.lower()]
    return (bold or files or [None])[0]


def find_font():
    env = os.environ.get("FONT_FILE")
    if env and Path(env).exists():
        return env
    local = sorted(glob.glob(str(HERE / "fonts" / "*.ttf")) + glob.glob(str(HERE / "fonts" / "*.otf")))
    if local:
        return local[0]

    style = os.environ.get("FONT_STYLE", "nastaliq").strip().lower()
    order = ["NotoNastaliqUrdu", "NotoNaskhArabic"] if style != "naskh" else ["NotoNaskhArabic"]
    for family in order:
        found = _pick(_glob_fonts(family))
        if found:
            if family == "NotoNaskhArabic" and style != "naskh":
                warn("Nastaliq font not found, using Naskh instead")
            return found
    for p in ("/usr/share/fonts/truetype/freefont/FreeSerifBold.ttf",
              "/usr/share/fonts/truetype/freefont/FreeSerif.ttf"):
        if Path(p).exists():
            return p
    sys.exit("No Urdu font found. On GitHub the workflow installs one for you. "
             "Locally, put an Urdu .ttf file in a folder called 'fonts' next to this script.")


def find_latin_font(fallback):
    for p in ("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
              "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf"):
        if Path(p).exists():
            return p
    return _pick(_glob_fonts("NotoSans-Bold")) or fallback


def find_emoji_font():
    files = _glob_fonts("NotoColorEmoji")
    return files[0] if files else None


def load_font(path, size, bold=True):
    f = ImageFont.truetype(path, size, layout_engine=ImageFont.Layout.RAQM)
    if bold:
        try:  # variable fonts: ask for bold; ordinary fonts raise, which is fine
            f.set_variation_by_axes([700])
        except Exception:
            pass
    return f


def is_rtl_text(s):
    return any("؀" <= c <= "ۿ" for c in s)


def text_width(draw, s, font):
    return draw.textlength(s, font=font, direction="rtl", language=LANG)


def wrap(draw, text, font, max_w):
    lines, cur = [], ""
    for word in text.split():
        trial = (cur + " " + word).strip()
        if not cur or text_width(draw, trial, font) <= max_w:
            cur = trial
        else:
            lines.append(cur)
            cur = word
    if cur:
        lines.append(cur)
    return lines


def render_card(text, font_path, start_size, max_w, max_lines, box_rgba,
                stroke=6, pad=(46, 34), radius=44, max_h=800,
                fill=(255, 255, 255), stroke_fill=(0, 0, 0)):
    """RGBA image: rounded box with centred right-to-left text, shrunk to fit."""
    scratch = ImageDraw.Draw(Image.new("RGBA", (10, 10)))
    size = start_size
    while True:
        font = load_font(font_path, size)
        lines = wrap(scratch, text, font, max_w)
        kw = dict(font=font, anchor="ma", direction="rtl", language=LANG, stroke_width=stroke)
        boxes = [scratch.textbbox((0, 0), l, **kw) for l in lines]
        line_h = max(b[3] - b[1] for b in boxes)
        gap = int(size * 0.14)
        bh = int(line_h * len(lines) + gap * (len(lines) - 1) + 2 * pad[1])
        if (len(lines) <= max_lines and bh <= max_h) or size <= 44:
            break
        size -= 4

    top = min(b[1] for b in boxes)
    text_w = max(b[2] - b[0] for b in boxes)
    bw = int(text_w + 2 * pad[0])
    img = Image.new("RGBA", (bw, bh), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rounded_rectangle((0, 0, bw - 1, bh - 1), radius=radius, fill=box_rgba)
    y = pad[1] - top
    for l in lines:
        d.text((bw / 2, y), l, fill=fill, stroke_fill=stroke_fill, **kw)
        y += line_h + gap
    return img


# ---- visual cards shown above the caption --------------------------------- #
def emoji_card(ch, accent, size=240):
    path = find_emoji_font()
    if not path:
        warn("no emoji font installed - skipping emoji icon")
        return None
    try:
        font = ImageFont.truetype(path, 109, layout_engine=ImageFont.Layout.BASIC)
        glyph = Image.new("RGBA", (200, 200), (0, 0, 0, 0))
        ImageDraw.Draw(glyph).text((20, 20), ch, font=font, embedded_color=True)
        box = glyph.getbbox()
        if not box:
            warn(f"emoji '{ch}' could not be drawn - skipping")
            return None
        glyph = glyph.crop(box)
        scale = (size * 0.66) / max(glyph.size)
        glyph = glyph.resize((max(1, int(glyph.width * scale)), max(1, int(glyph.height * scale))),
                             Image.LANCZOS)
        card = Image.new("RGBA", (size, size), (0, 0, 0, 0))
        d = ImageDraw.Draw(card)
        d.ellipse((0, 0, size - 1, size - 1), fill=(0, 0, 0, 125), outline=accent + (255,), width=7)
        card.alpha_composite(glyph, ((size - glyph.width) // 2, (size - glyph.height) // 2))
        return card
    except Exception as e:
        warn(f"emoji icon failed ({e}) - skipping")
        return None


def stat_card(value, main_font, latin_font, accent):
    rtl = is_rtl_text(value)
    path = main_font if rtl else latin_font
    scratch = ImageDraw.Draw(Image.new("RGBA", (10, 10)))
    size = 210
    kw = dict(direction="rtl", language=LANG) if rtl else {}
    while True:
        font = load_font(path, size, bold=not rtl)
        box = scratch.textbbox((0, 0), value, font=font, stroke_width=5, **kw)
        if box[2] - box[0] <= 820 or size <= 70:
            break
        size -= 10
    w, h = box[2] - box[0] + 120, box[3] - box[1] + 80
    img = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rounded_rectangle((0, 0, w - 1, h - 1), radius=50, fill=(0, 0, 0, 150),
                        outline=accent + (255,), width=6)
    d.text((60 - box[0], 40 - box[1]), value, font=font, fill=accent + (255,),
           stroke_width=5, stroke_fill=(0, 0, 0, 255), **kw)
    return img


def bar_card(spec, main_font, latin_font, accent):
    rows = []
    for part in spec.split("|"):
        if "=" not in part:
            continue
        label, value = part.rsplit("=", 1)
        try:
            rows.append((label.strip(), max(0.0, min(100.0, float(value.strip().rstrip("%"))))))
        except ValueError:
            continue
    rows = rows[:4]
    if not rows:
        warn(f"bar tag not understood: {spec!r}")
        return None
    cw, pad, row_h = 940, 50, 150
    ch = row_h * len(rows) + 2 * 30
    img = Image.new("RGBA", (cw, ch), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rounded_rectangle((0, 0, cw - 1, ch - 1), radius=44, fill=(0, 0, 0, 150))
    label_font = load_font(main_font, 58)
    value_font = load_font(latin_font, 48, bold=False)
    track_w = cw - 2 * pad
    for i, (label, value) in enumerate(rows):
        y = 30 + i * row_h
        d.text((cw - pad, y + 4), label, font=label_font, fill=(255, 255, 255, 255), anchor="ra",
               direction="rtl", language=LANG, stroke_width=3, stroke_fill=(0, 0, 0, 255))
        d.text((pad, y + 22), f"{value:g}%", font=value_font, fill=accent + (255,), anchor="la")
        ty = y + 96
        d.rounded_rectangle((pad, ty, pad + track_w, ty + 30), radius=15, fill=(255, 255, 255, 70))
        fw = int(track_w * value / 100)
        if fw >= 4:
            d.rounded_rectangle((pad + track_w - fw, ty, pad + track_w, ty + 30), radius=15,
                                fill=accent + (255,))
    return img


def make_background(idx, path):
    top, bottom, accent = PALETTES[idx % len(PALETTES)]
    bw, bh = int(W * 1.15), int(H * 1.15)
    grad = Image.linear_gradient("L").resize((bw, bh))
    bg = ImageOps.colorize(grad, black=top, white=bottom).convert("RGBA")
    glow = Image.new("RGBA", (bw, bh), (0, 0, 0, 0))
    d = ImageDraw.Draw(glow)
    d.ellipse((-200, 200, 700, 1100), fill=accent + (70,))
    d.ellipse((600, 1300, 1400, 2100), fill=accent + (55,))
    d.ellipse((300, -300, 1100, 400), fill=(255, 255, 255, 35))
    glow = glow.filter(ImageFilter.GaussianBlur(110))
    Image.alpha_composite(bg, glow).convert("RGB").save(path)


# --------------------------------------------------------------------------- #
# Footage: your own clips folder and Pixabay
# --------------------------------------------------------------------------- #
class Footage:
    def __init__(self, work_dir, clips_dir, api_key):
        self.dir = Path(work_dir)
        self.local = []
        if clips_dir and Path(clips_dir).is_dir():
            self.local = sorted(p for p in Path(clips_dir).iterdir() if p.suffix.lower() in VIDEO_EXT)
        self.api_key = api_key
        self.api_failures = 0
        self.used_local, self.used_ids = set(), set()
        self.used_pixabay = False

    def get(self, keyword):
        kw = (keyword or "").strip()
        if kw and self.local:
            hits = [p for p in self.local if kw.lower() in p.stem.lower() and p not in self.used_local]
            if hits:
                return self._local(hits[0])
        if kw and self.api_key and self.api_failures < 3:
            p = self._pixabay(kw)
            if p:
                return p
        if self.local:
            free = [p for p in self.local if p not in self.used_local]
            if not free:
                self.used_local.clear()
                free = self.local
            return self._local(free[0])
        return None

    def _local(self, p):
        self.used_local.add(p)
        return str(p)

    def _pixabay(self, kw):
        query = urllib.parse.urlencode({"key": self.api_key, "q": kw[:90], "per_page": 30,
                                        "safesearch": "true"})
        try:
            req = urllib.request.Request("https://pixabay.com/api/videos/?" + query,
                                         headers={"User-Agent": "urdu-shorts/2.0"})
            data = json.loads(urllib.request.urlopen(req, timeout=30).read().decode("utf-8"))
            hits = [h for h in data.get("hits", []) if h.get("id") not in self.used_ids]
            random.shuffle(hits)
            for h in hits[:8]:
                vids = h.get("videos", {})
                for quality in ("large", "medium", "small"):
                    cand = vids.get(quality) or {}
                    url, size = cand.get("url"), cand.get("size") or 0
                    if not url or (quality == "large" and size > 45_000_000):
                        continue
                    dest = self.dir / f"px_{h['id']}.mp4"
                    if not dest.exists():
                        dl = urllib.request.Request(url, headers={"User-Agent": "urdu-shorts/2.0"})
                        with urllib.request.urlopen(dl, timeout=90) as r, open(dest, "wb") as f:
                            shutil.copyfileobj(r, f)
                    self.used_ids.add(h["id"])
                    self.api_failures = 0
                    self.used_pixabay = True
                    return str(dest)
            warn(f"no Pixabay footage found for '{kw}'")
            return None
        except Exception as e:
            self.api_failures += 1
            warn(f"Pixabay problem ({e})")
            return None


# --------------------------------------------------------------------------- #
# Voice and sound
# --------------------------------------------------------------------------- #
async def synth_all(items, mp3_paths):
    import edge_tts  # imported here so --fake-voice works without it
    for (text, rate), path in zip(items, mp3_paths):
        last_error = None
        for attempt in range(4):
            try:
                kwargs = {"rate": rate}
                if PITCH:
                    kwargs["pitch"] = PITCH
                await edge_tts.Communicate(text, VOICE, **kwargs).save(str(path))
                if Path(path).stat().st_size > 1000:
                    break
            except Exception as e:  # network hiccup: wait and retry
                last_error = e
                await asyncio.sleep(2 * (attempt + 1))
        else:
            raise RuntimeError(f"Voice generation failed for: {text[:40]}... ({last_error})")


def to_wav(src, dst):
    subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-i", str(src), "-ar", str(SAMPLE_RATE),
                    "-ac", "1", "-c:a", "pcm_s16le", str(dst)], check=True)


def fake_wav(text, dst):
    """Quiet test tone, only used with --fake-voice (no internet needed)."""
    seconds = max(1.2, 0.075 * len(text))
    n = int(SAMPLE_RATE * seconds)
    a = array.array("h", (int(2500 * math.sin(2 * math.pi * 220 * i / SAMPLE_RATE)) for i in range(n)))
    if sys.byteorder == "big":
        a.byteswap()
    with wave.open(str(dst), "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SAMPLE_RATE)
        w.writeframes(a.tobytes())


def read_wav_samples(path):
    with wave.open(str(path), "rb") as r:
        a = array.array("h")
        a.frombytes(r.readframes(r.getnframes()))
    if sys.byteorder == "big":
        a.byteswap()
    return a


def add_whoosh(pcm, start_sec, seed):
    """Soft noise sweep so every cut has a little 'swoosh'."""
    rnd = random.Random(seed)
    n, off, y = int(SAMPLE_RATE * 0.45), int(start_sec * SAMPLE_RATE), 0.0
    for i in range(n):
        x = i / n
        env = math.sin(math.pi * x) ** 2
        y += (0.04 + 0.45 * x) * ((rnd.random() * 2 - 1) - y)
        j = off + i
        if 0 <= j < len(pcm):
            pcm[j] = max(-32768, min(32767, pcm[j] + int(9000 * env * y)))


def build_voice_track(lines, workdir, fake):
    """Return (voice.wav, [(start, end) per line], total duration, cut points)."""
    wavs = []
    if fake:
        for i, line in enumerate(lines):
            p = workdir / f"line_{i}.wav"
            fake_wav(line["text"], p)
            wavs.append(p)
    else:
        items = []
        for line in lines:
            rate = line["tags"].get("rate", RATE)
            items.append((line["text"], rate if re.fullmatch(r"[+-]\d{1,3}%", rate) else RATE))
        mp3s = [workdir / f"line_{i}.mp3" for i in range(len(lines))]
        asyncio.run(synth_all(items, mp3s))
        for i, m in enumerate(mp3s):
            p = workdir / f"line_{i}.wav"
            to_wav(m, p)
            wavs.append(p)

    def silence(sec):
        return array.array("h", bytes(2 * int(SAMPLE_RATE * sec)))

    pcm = array.array("h")
    pcm.extend(silence(LEAD))
    times, t = [], LEAD
    for i, p in enumerate(wavs):
        a = read_wav_samples(p)
        dur = len(a) / SAMPLE_RATE
        times.append((t, t + dur))
        pcm.extend(a)
        t += dur
        if i < len(wavs) - 1:
            try:
                pause = max(0.0, min(2.5, float(lines[i]["tags"].get("pause", 0))))
            except ValueError:
                pause = 0.0
            pcm.extend(silence(GAP + pause))
            t += GAP + pause
    pcm.extend(silence(TAIL))
    total = len(pcm) / SAMPLE_RATE

    # cut points sit in the middle of the pause between two lines
    cuts = [0.0] + [(times[i - 1][1] + times[i][0]) / 2 for i in range(1, len(times))] + [total]
    if SFX:
        for k, c in enumerate(cuts[1:-1]):
            add_whoosh(pcm, c - 0.18, seed=k + 1)

    out = workdir / "voice.wav"
    if sys.byteorder == "big":
        pcm.byteswap()
    with wave.open(str(out), "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SAMPLE_RATE)
        w.writeframes(pcm.tobytes())
    return out, times, total, cuts


# --------------------------------------------------------------------------- #
# One video
# --------------------------------------------------------------------------- #
def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("ffmpeg failed:\n" + r.stderr[-1800:])


def make_segment(src, dur, seg_idx, gradient_path, out):
    cmd = ["ffmpeg", "-y", "-loglevel", "error"]
    if src:
        d = 1 if seg_idx % 2 == 0 else -1
        cmd += ["-stream_loop", "-1", "-i", src]
        vf = (f"fps={FPS},scale={int(W * 1.15)}:{int(H * 1.12)}:force_original_aspect_ratio=increase,"
              f"crop={W}:{H}:x='clip((iw-{W})/2+{d}*70*(t-{dur:.3f}/2),0,iw-{W})':y='(ih-{H})/2',"
              f"drawbox=x=0:y=0:w=iw:h=ih:color=black@0.38:t=fill,format=yuv420p")
    else:
        cmd += ["-loop", "1", "-framerate", str(FPS), "-i", str(gradient_path)]
        vf = (f"crop={W}:{H}:x='(iw-{W})/2*(1+sin(2*PI*t/22+{seg_idx}))':"
              f"y='(ih-{H})/2*(1+cos(2*PI*t/28+{seg_idx}))',fps={FPS},format=yuv420p")
    cmd += ["-t", f"{dur:.3f}", "-vf", vf, "-an", "-c:v", "libx264", "-preset", "veryfast",
            "-crf", "20", "-r", str(FPS), str(out)]
    run(cmd)


def make_video(index, video, out_dir, main_font, footage, music_file, fake):
    out_dir.mkdir(parents=True, exist_ok=True)
    name = f"short_{index:02d}"
    palette = PALETTES[(index - 1) % len(PALETTES)]
    accent = palette[2]
    latin_font = find_latin_font(main_font)

    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        voice_wav, times, dur, cuts = build_voice_track(video["lines"], tmp, fake)

        # 1) background: one clip (or gradient) per line, cut in the pauses
        gradient = tmp / "gradient.png"
        make_background(index - 1, gradient)
        seg_files = []
        for i, line in enumerate(video["lines"]):
            keyword = line["tags"].get("search") or video["search"]
            src = footage.get(keyword)
            seg = tmp / f"seg_{i}.mp4"
            make_segment(src, cuts[i + 1] - cuts[i], i, gradient, seg)
            seg_files.append(seg)
        listing = tmp / "list.txt"
        listing.write_text("".join(f"file '{p}'\n" for p in seg_files), encoding="utf-8")
        background = tmp / "background.mp4"
        run(["ffmpeg", "-y", "-loglevel", "error", "-f", "concat", "-safe", "0", "-i", str(listing),
             "-c", "copy", str(background)])

        # 2) graphics
        bar_png = tmp / "bar.png"
        Image.new("RGBA", (W, 14), accent + (235,)).save(bar_png)
        banner = render_card(video["title"], main_font, 68, 880, 2, accent + (235,),
                             stroke=0, fill=(20, 20, 30), pad=(44, 26), radius=60, max_h=260)
        banner_png = tmp / "banner.png"
        banner.save(banner_png)

        # elements: (png, x, y, show_from, show_to, animated)
        elements = [(bar_png, None, 40, None, None, "bar"),
                    (banner_png, (W - banner.size[0]) // 2, 190, None, None, "static")]
        for i, line in enumerate(video["lines"]):
            start = times[i][0]
            show_from = max(0.0, start - 0.05)
            show_to = (times[i + 1][0] - 0.05) if i + 1 < len(times) else dur
            cap = render_card(line["text"], main_font, 92, 900, 5, (0, 0, 0, 150))
            cap_top = int(min(1130 - cap.size[1] / 2, 1470 - cap.size[1]))
            cap_top = max(cap_top, 520)

            tags = line["tags"]
            visual = None
            if "bar" in tags:
                visual = bar_card(tags["bar"], main_font, latin_font, accent)
            elif "stat" in tags:
                visual = stat_card(tags["stat"], main_font, latin_font, accent)
            elif "emoji" in tags:
                visual = emoji_card(tags["emoji"], accent)
            if visual is not None:
                room = cap_top - 30 - 340
                if room < 110:
                    visual = None
                elif visual.size[1] > room:
                    s = room / visual.size[1]
                    visual = visual.resize((int(visual.size[0] * s), room), Image.LANCZOS)
            if visual is not None:
                vp = tmp / f"vis_{i}.png"
                visual.save(vp)
                vy = max(340, cap_top - 30 - visual.size[1])
                elements.append((vp, (W - visual.size[0]) // 2, vy, show_from, show_to, "pop"))
            cp = tmp / f"cap_{i}.png"
            cap.save(cp)
            elements.append((cp, (W - cap.size[0]) // 2, cap_top, show_from + 0.06, show_to, "pop"))

        # 3) put it all together
        cmd = ["ffmpeg", "-y", "-loglevel", "error", "-i", str(background)]
        for png, _x, _y, sf, st, kind in elements:
            if kind == "pop":
                cmd += ["-loop", "1", "-framerate", str(FPS), "-t", f"{st - sf + 0.3:.3f}", "-i", str(png)]
            else:
                cmd += ["-i", str(png)]
        cmd += ["-i", str(voice_wav)]
        audio_idx = 1 + len(elements)
        if music_file:
            cmd += ["-stream_loop", "-1", "-i", str(music_file)]

        fc, label = [], "0:v"
        for n, (png, x, y, sf, st, kind) in enumerate(elements, start=1):
            out_label = f"o{n}"
            if kind == "bar":
                fc.append(f"[{label}][{n}:v]overlay=x='-w+w*t/{dur:.3f}':y={y}[{out_label}]")
            elif kind == "static":
                fc.append(f"[{label}][{n}:v]overlay=x={x}:y={y}[{out_label}]")
            else:
                fc.append(f"[{n}:v]format=rgba,fade=t=in:st=0:d=0.14:alpha=1,setpts=PTS+{sf:.3f}/TB[e{n}]")
                fc.append(f"[{label}][e{n}]overlay=x={x}:y='{y}+36*max(0,1-(t-{sf:.3f})/0.16)':"
                          f"enable='between(t,{sf:.3f},{st:.3f})':eof_action=pass[{out_label}]")
            label = out_label
        fc.append(f"[{label}]format=yuv420p[v]")
        if music_file:
            fc.append(f"[{audio_idx + 1}:a]volume={MUSIC_VOLUME},atrim=0:{dur:.3f}[m]")
            fc.append(f"[{audio_idx}:a][m]amix=inputs=2:duration=first:normalize=0[a]")
            audio_map = "[a]"
        else:
            audio_map = f"{audio_idx}:a"

        out_mp4 = out_dir / f"{name}.mp4"
        cmd += ["-filter_complex", ";".join(fc), "-map", "[v]", "-map", audio_map,
                "-c:v", "libx264", "-preset", "veryfast", "-crf", "21", "-r", str(FPS),
                "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "160k", "-t", f"{dur:.3f}",
                "-movflags", "+faststart", str(out_mp4)]
        run(cmd)

    tags = video["tags"] or "#Shorts #اردو"
    if "#shorts" not in tags.lower():
        tags += " #Shorts"
    credit = "\n\nStock footage: Pixabay" if footage.used_pixabay else ""
    (out_dir / f"{name}.txt").write_text(
        f"TITLE:\n{video['title']} #Shorts\n\nDESCRIPTION:\n{video['title']}\n\n{tags}{credit}\n",
        encoding="utf-8")
    return out_mp4, dur


# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description="Make Urdu YouTube Shorts from scripts.txt")
    ap.add_argument("--scripts", default="scripts.txt")
    ap.add_argument("--out", default="out")
    ap.add_argument("--clips", default=str(HERE / "clips"), help="folder with your own video clips")
    ap.add_argument("--music", default=str(HERE / "music"), help="folder with a background music file")
    ap.add_argument("--only", type=int, help="only make video number N")
    ap.add_argument("--fake-voice", action="store_true",
                    help="test mode: placeholder beeps instead of the real voice (no internet)")
    args = ap.parse_args()

    if not features.check("raqm"):
        sys.exit("Urdu text shaping is missing (Pillow needs libraqm). "
                 "On Ubuntu run: sudo apt-get install -y libraqm0 libfribidi0")
    if subprocess.run(["ffmpeg", "-version"], capture_output=True).returncode != 0:
        sys.exit("ffmpeg is not installed.")

    videos = parse_scripts(Path(args.scripts).read_text(encoding="utf-8"))
    if not videos:
        sys.exit(f"No scripts found in {args.scripts}.")

    main_font = find_font()
    music_file = None
    if Path(args.music).is_dir():
        found = sorted(p for p in Path(args.music).iterdir() if p.suffix.lower() in MUSIC_EXT)
        music_file = found[0] if found else None

    work = Path(tempfile.mkdtemp(prefix="footage_"))
    try:
        footage = Footage(work, args.clips, PIXABAY_KEY)
        print(f"Font: {main_font}")
        print(f"Voice: {'(test beeps)' if args.fake_voice else VOICE}   Videos: {len(videos)}")
        print(f"Footage: {len(footage.local)} own clips, Pixabay {'on' if PIXABAY_KEY else 'off'}   "
              f"Music: {music_file.name if music_file else 'none'}")
        for i, v in enumerate(videos, start=1):
            if args.only and i != args.only:
                continue
            mp4, dur = make_video(i, v, Path(args.out), main_font, footage, music_file, args.fake_voice)
            note = "  <-- over 60s, consider trimming" if dur > 60 else ""
            print(f"[{i}/{len(videos)}] {mp4}  ({dur:.1f}s){note}")
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
