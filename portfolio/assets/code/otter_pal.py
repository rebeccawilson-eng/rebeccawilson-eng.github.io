#!/usr/bin/env python3
"""
Otter Pal - a retro pixel-art otter that lives in a picture frame.

* Shows the time and date
* Mirrors your real weather (sun, clouds, drizzle, rain, storms, snow, fog,
  stars and moon at night) using the free Open-Meteo API (no key needed)
  plus a rainbow when the rain stops
* Seasons: blossom in spring, fireflies in summer, falling leaves in autumn,
  a bare tree in winter
* Holidays: a Halloween pumpkin and bats, Christmas lights, New Year fireworks
* The otter swims in the pond on warm days, dresses for the weather
  (sunglasses, scarf, beanie, wellies) and has duck and butterfly visitors
* Sleeps from 22:00 to 08:00 (configurable) with a yawn and a morning stretch
* Reminds you of birthdays and throws a party on the day
* Tap the screen (if it's a touchscreen) to give the otter a fish

Add birthdays and send the otter messages from any phone on your Wi-Fi:
    http://<your-pi>.local:8080

Testing on a normal computer:
    python3 otter_pal.py --windowed
    python3 otter_pal.py --windowed --weather rain --time 14:00
    python3 otter_pal.py --windowed --demo        (cycles every weather)
    python3 otter_pal.py --windowed --date 2026-12-31 --time 23:30
"""

import argparse
import hashlib
import datetime as dt
import html
import json
import math
import mmap
import os
import random
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
import pygame  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(HERE, "config.json")
BIRTHDAYS_PATH = os.path.join(HERE, "birthdays.json")
MESSAGE_PATH = os.path.join(HERE, "message.json")
STATE_PATH = os.path.join(HERE, "state.json")
SETTINGS_PATH = os.path.join(HERE, "settings.json")

W, H = 200, 120   # the otter's world, in chunky retro pixels
GRASS_Y = 88
OTTER_Y = 66
BED_X = 33           # otter x when standing at its front door
HOUSE_X = 34         # left edge of the house walls
DOOR = (40, 67, 18, 26)
WINDOW = (62, 67, 10, 9)
LEAF_PILE_X = 94
CAMP_X = 116
PUDDLES = (56, 82, 100)
POND_EDGE_X = 108
SUN_X, SUN_Y = 104, 14
FPS = 15

DEFAULT_CONFIG = {
    "place": "Amsterdam",
    "latitude": 52.37,
    "longitude": 4.90,
    "temperature_unit": "celsius",
    "clock_24h": True,
    "sleep_time": "22:00",
    "wake_time": "08:00",
    "weather_refresh_minutes": 10,
    "birthday_lookahead_days": 7,
    "web_port": 8080,
    "camera": True,
    "camera_mirror": True,
    "camera_sensitivity": 1.0,
    "detail": "auto",
}

DEMO_ORDER = ["clear", "cloudy", "fog", "drizzle", "rain", "partly", "storm", "snow"]
WEATHER_KINDS = ["clear", "partly", "cloudy", "fog", "drizzle", "rain", "storm", "snow"]
RAINY = ("drizzle", "rain", "storm")
GREY = ("cloudy", "fog", "drizzle", "rain", "storm", "snow")


# --------------------------------------------------------------------------
# Config & time helpers
# --------------------------------------------------------------------------

def load_config():
    cfg = dict(DEFAULT_CONFIG)
    try:
        with open(CONFIG_PATH) as f:
            cfg.update(json.load(f))
    except FileNotFoundError:
        pass
    except Exception as e:
        print("[config] problem reading config.json, using defaults:", e)
    return cfg


def parse_hm(s):
    h, m = s.strip().split(":")
    return dt.time(int(h), int(m))


def is_sleep_time(now, start, wake):
    t = now.time()
    if start > wake:                      # e.g. 22:00 -> 08:00 crosses midnight
        return t >= start or t < wake
    return start <= t < wake


def day_phase(now, sunrise, sunset):
    sr = sunrise.time() if sunrise else dt.time(7, 30)
    ss = sunset.time() if sunset else dt.time(18, 30)
    m = now.hour * 60 + now.minute
    r = sr.hour * 60 + sr.minute
    s = ss.hour * 60 + ss.minute
    if abs(m - r) <= 40 or abs(m - s) <= 40:
        return "dawn"
    return "day" if r < m < s else "night"


def season_of(d):
    m = d.month
    if 3 <= m <= 5:
        return "spring"
    if 6 <= m <= 8:
        return "summer"
    if 9 <= m <= 11:
        return "autumn"
    return "winter"


def holidays_for(now):
    m, d = now.month, now.day
    h = set()
    if m == 10 and d >= 24:
        h.add("halloween")
    if m == 10 and d == 31:
        h.add("halloween_day")
    if m == 12 and d <= 26:
        h.add("christmas")
    if m == 12 and d == 25:
        h.add("christmas_day")
    if (m == 12 and d == 31 and now.hour >= 17) or (m == 1 and d == 1 and now.time() < dt.time(0, 45)):
        h.add("nye")                       # the otter stays up for the fireworks
    if m == 1 and d == 1:
        h.add("newyear")
    kings = dt.date(now.year, 4, 27)
    if kings.weekday() == 6:                  # moves to Saturday when it falls on a Sunday
        kings = dt.date(now.year, 4, 26)
    if now.date() == kings:
        h.add("kingsday")
    if (m == 11 and d >= 14) or (m == 12 and d <= 5):
        h.add("sinterklaas")                  # shoe out by the door
    if m == 12 and d == 5:
        h.add("pakjesavond")
    if m == 12 and d == 31:
        h.add("oudjaar")                      # oliebollen day
    return h


def day_hash(d, salt):
    """A stable pseudo-random number for a date (same after restarts)."""
    return int(hashlib.md5(f"{d.isoformat()}:{salt}".encode()).hexdigest()[:8], 16)


def moon_phase(now):
    """0 = new moon, 0.5 = full moon."""
    ref = dt.datetime(2000, 1, 6, 18, 14)
    return ((now - ref).total_seconds() / 86400 / 29.530588853) % 1.0


def world_otter_day(year):
    """Last Wednesday in May."""
    d = dt.date(year, 5, 31)
    while d.weekday() != 2:
        d -= dt.timedelta(days=1)
    return d


# --------------------------------------------------------------------------
# Weather (Open-Meteo, free, no API key)
# --------------------------------------------------------------------------

def classify(code):
    if code in (0, 1):
        return "clear"
    if code == 2:
        return "partly"
    if code == 3:
        return "cloudy"
    if code in (45, 48):
        return "fog"
    if 51 <= code <= 57:
        return "drizzle"
    if 61 <= code <= 67 or 80 <= code <= 82:
        return "rain"
    if 71 <= code <= 77 or code in (85, 86):
        return "snow"
    if code >= 95:
        return "storm"
    return "cloudy"


class Weather:
    def __init__(self, cfg, forced=None):
        self.cfg = cfg
        self.forced = forced
        self.lock = threading.Lock()
        self.kind, self.temp, self.ok = "clear", None, False
        self.wind = None
        self.kp, self.kp_checked = None, 0.0
        self.hourly = []                      # [(datetime, rain probability %, mm)]
        self.sunrise = self.sunset = None
        threading.Thread(target=self._loop, daemon=True).start()

    def snapshot(self):
        with self.lock:
            s = dict(kind=self.kind, temp=self.temp, ok=self.ok, wind=self.wind, kp=self.kp,
                     hourly=list(self.hourly),
                     sunrise=self.sunrise, sunset=self.sunset)
        if self.forced:
            s["kind"], s["ok"] = self.forced, True
            if s["temp"] is None:
                s["temp"] = {"snow": -2, "storm": 14, "clear": 18}.get(self.forced, 11)
            if s["wind"] is None:
                s["wind"] = {"storm": 45, "rain": 20}.get(self.forced, 10)
        return s

    def _loop(self):
        while True:
            try:
                self._fetch()
                wait = max(2, self.cfg["weather_refresh_minutes"]) * 60
            except Exception as e:
                print(f"[weather] couldn't update ({e}); retrying in 1 min")
                wait = 60
            time.sleep(wait)

    def _fetch_kp(self):
        """Planetary K-index from NOAA; Kp 6+ can mean aurora over the Netherlands."""
        if time.time() - self.kp_checked < 1800:
            return
        self.kp_checked = time.time()
        try:
            req = urllib.request.Request("https://services.swpc.noaa.gov/products/noaa-planetary-k-index.json",
                                         headers={"User-Agent": "otter-pal/1.0"})
            with urllib.request.urlopen(req, timeout=15) as r:
                data = json.load(r)
            last = data[-1]
            if isinstance(last, dict):
                val = last.get("Kp", last.get("kp_index", last.get("estimated_kp")))
            else:
                val = last[1]
            with self.lock:
                self.kp = float(val)
        except Exception as e:
            print(f"[aurora] couldn't read the Kp index ({e})")

    @staticmethod
    def _get(params):
        req = urllib.request.Request("https://api.open-meteo.com/v1/forecast?" + urllib.parse.urlencode(params),
                                     headers={"User-Agent": "otter-pal/1.0"})
        with urllib.request.urlopen(req, timeout=15) as r:
            return json.load(r)

    def _fetch(self):
        self._fetch_kp()
        params = {
            "latitude": self.cfg["latitude"],
            "longitude": self.cfg["longitude"],
            "current": "temperature_2m,weather_code,wind_speed_10m",
            "daily": "sunrise,sunset",
            "hourly": "precipitation_probability,precipitation",
            "forecast_hours": 12,
            "temperature_unit": self.cfg["temperature_unit"],
            "timezone": "auto",
            "forecast_days": 1,
        }
        try:
            data = self._get(params)
        except urllib.error.HTTPError as e:
            # if the full request is ever refused, fall back to the basics (no rain warning)
            print(f"[weather] full forecast refused ({e}); using the basic one")
            for k in ("hourly", "forecast_hours"):
                params.pop(k)
            data = self._get(params)
        cur, daily = data["current"], data.get("daily", {})
        sr = daily.get("sunrise", [None])[0]
        ss = daily.get("sunset", [None])[0]
        with self.lock:
            self.kind = classify(int(cur["weather_code"]))
            self.temp = float(cur["temperature_2m"])
            self.wind = float(cur.get("wind_speed_10m") or 0)    # km/h
            hr = data.get("hourly", {})
            self.hourly = [(dt.datetime.fromisoformat(tm), p or 0, mm or 0)
                           for tm, p, mm in zip(hr.get("time", []), hr.get("precipitation_probability", []),
                                                hr.get("precipitation", []))]
            self.sunrise = dt.datetime.fromisoformat(sr) if sr else None
            self.sunset = dt.datetime.fromisoformat(ss) if ss else None
            self.ok = True


# --------------------------------------------------------------------------
# Birthdays
# --------------------------------------------------------------------------

def next_occurrence(month, day, today):
    for year in (today.year, today.year + 1):
        try:
            d = dt.date(year, month, day)
        except ValueError:                # 29 Feb in a non-leap year
            d = dt.date(year, 2, 28)
        if d >= today:
            return d


class BirthdayBook:
    def __init__(self, path):
        self.path = path
        self.lock = threading.Lock()
        self.mtime = None
        self.items = self._load()

    def _load(self):
        try:
            self.mtime = os.path.getmtime(self.path)
            with open(self.path) as f:
                raw = json.load(f)
        except FileNotFoundError:
            return []
        except Exception as e:
            print("[birthdays] couldn't read birthdays.json:", e)
            return []
        items = []
        for b in raw:
            try:
                items.append({"id": b.get("id") or uuid.uuid4().hex[:8],
                              "name": str(b["name"])[:30],
                              "month": int(b["month"]), "day": int(b["day"]),
                              "year": int(b["year"]) if b.get("year") else None})
            except Exception:
                print("[birthdays] skipping bad entry:", b)
        return items

    def maybe_reload(self):
        """Pick up hand edits to birthdays.json."""
        try:
            m = os.path.getmtime(self.path)
        except FileNotFoundError:
            return
        if m != self.mtime:
            with self.lock:
                self.items = self._load()

    def _save(self):
        tmp = self.path + ".tmp"
        with open(tmp, "w") as f:
            json.dump(self.items, f, indent=2)
        os.replace(tmp, self.path)
        self.mtime = os.path.getmtime(self.path)

    def add(self, name, month, day, year=None):
        name = " ".join(name.split())[:30]
        if not name:
            raise ValueError("Please enter a name")
        dt.date(2000, month, day)         # validates (2000 is a leap year)
        if year is not None and not (1900 <= year <= dt.date.today().year):
            raise ValueError("That year doesn't look right")
        with self.lock:
            self.items.append({"id": uuid.uuid4().hex[:8], "name": name,
                               "month": month, "day": day, "year": year})
            self._save()

    def remove(self, bid):
        with self.lock:
            self.items = [b for b in self.items if b["id"] != bid]
            self._save()

    def upcoming(self, today, days_ahead=366):
        out = []
        with self.lock:
            items = list(self.items)
        for b in items:
            occ = next_occurrence(b["month"], b["day"], today)
            n = (occ - today).days
            if n <= days_ahead:
                age = occ.year - b["year"] if b["year"] else None
                out.append((n, b, age))
        out.sort(key=lambda x: (x[0], x[1]["name"].lower()))
        return out


def possessive(name):
    return name + "'" if name.lower().endswith("s") else name + "'s"


def reminder_text(days, b, age):
    p = possessive(b["name"])
    s = f"{p} birthday is tomorrow!" if days == 1 else f"{p} birthday in {days} days"
    return s + (f" - turns {age}" if age else "")




class MessageBoard:
    """A note you send from your phone, shown in a speech bubble."""

    def __init__(self, path):
        self.path = path
        self.lock = threading.Lock()
        self.text, self.until = None, None
        try:
            with open(path) as f:
                d = json.load(f)
            self.text = d.get("text") or None
            self.until = dt.datetime.fromisoformat(d["until"]) if d.get("until") else None
        except FileNotFoundError:
            pass
        except Exception as e:
            print("[message] couldn't read message.json:", e)

    def current(self):
        with self.lock:
            if self.text and (self.until is None or dt.datetime.now() < self.until):
                return self.text
        return None

    def _save(self):
        tmp = self.path + ".tmp"
        with open(tmp, "w") as f:
            json.dump({"text": self.text,
                       "until": self.until.isoformat() if self.until else None}, f)
        os.replace(tmp, self.path)

    def set(self, text, minutes):
        text = " ".join(text.split())[:60]
        if not clean_text(text).strip():
            raise ValueError("Type a message with some letters or numbers in it")
        with self.lock:
            self.text = text
            self.until = dt.datetime.now() + dt.timedelta(minutes=minutes) if minutes else None
            self._save()

    def clear(self):
        with self.lock:
            self.text, self.until = None, None
            self._save()


TREASURES = {
    "pebble":      ((150, 150, 158), [".1.", "111"]),
    "blue pebble": ((110, 140, 200), [".1.", "111"]),
    "shell":       ((250, 196, 206), ["1.1", "111", ".1."]),
    "sea glass":   ((120, 210, 180), ["11", "11"]),
    "feather":     ((240, 240, 250), ["..1", ".1.", "1.."]),
    "button":      ((220, 80, 80), ["111", "1.1", "111"]),
    "acorn":       ((150, 100, 50), ["111", ".1."]),
    "conker":      ((120, 60, 30), [".1.", "111", ".1."]),
}


class OtterState:
    """Things the otter keeps between restarts: its treasures and start date."""

    def __init__(self, path, persist=True):
        self.path, self.persist = path, persist
        self.data = {"started": dt.date.today().isoformat(), "treasures": [], "last_find": None,
                     "garden_planted": dt.date.today().isoformat(), "tricks_announced": 1}
        try:
            with open(path) as f:
                self.data.update(json.load(f))
        except FileNotFoundError:
            self._save()
        except Exception as e:
            print("[state] couldn't read state.json:", e)

    def _save(self):
        if not self.persist:
            return
        tmp = self.path + ".tmp"
        with open(tmp, "w") as f:
            json.dump(self.data, f, indent=1)
        os.replace(tmp, self.path)

    def find_treasure(self, today, season):
        """One new treasure per day. Returns its name the first time each day."""
        if self.data.get("last_find") == today.isoformat():
            return None
        names = ["pebble", "pebble", "blue pebble", "shell", "shell", "sea glass", "feather", "button"]
        if season == "autumn":
            names += ["acorn", "acorn", "conker", "conker"]
        name = random.choice(names)
        self.data["treasures"] = (self.data["treasures"] + [name])[-60:]
        self.data["last_find"] = today.isoformat()
        self._save()
        return name

    @property
    def treasures(self):
        return self.data["treasures"]

    def days_since_start(self, today):
        try:
            return (today - dt.date.fromisoformat(self.data["started"])).days
        except Exception:
            return 0

    def garden_stage(self, today):
        """-1 = resting for winter, 0 seeds ... 4 ripe, 5 = time to harvest."""
        if today.month in (12, 1, 2):
            return -1
        try:
            planted = dt.date.fromisoformat(self.data.get("garden_planted"))
        except Exception:
            planted = today
        if planted.month in (12, 1, 2) or planted > today:
            planted = max(dt.date(today.year, 3, 1), planted if planted <= today else today)
            self.data["garden_planted"] = planted.isoformat()
            self._save()
        d = (today - planted).days
        for stage, limit in enumerate((4, 10, 20, 30, 44)):
            if d < limit:
                return stage
        return 5

    def replant(self, today):
        self.data["garden_planted"] = today.isoformat()
        self._save()

    def tricks_known(self, today):
        return max(1, min(len(TRICKS), self.days_since_start(today) // 7 + 1))

    def announce_trick(self, n):
        self.data["tricks_announced"] = n
        self._save()


WORDS = [
    ("gezellig", "cosy, nice and friendly"), ("lekker", "tasty, nice"), ("fiets", "bike"),
    ("regen", "rain"), ("zon", "sun"), ("wolk", "cloud"), ("wind", "wind"), ("sneeuw", "snow"),
    ("otter", "otter"), ("vis", "fish"), ("vijver", "pond"), ("huis", "house"), ("tuin", "garden"),
    ("bloem", "flower"), ("boom", "tree"), ("blad", "leaf"), ("steen", "stone"), ("schelp", "shell"),
    ("eend", "duck"), ("kikker", "frog"), ("slak", "snail"), ("reiger", "heron"), ("gans", "goose"),
    ("vlieger", "kite"), ("paraplu", "umbrella"), ("laarzen", "boots"), ("sjaal", "scarf"),
    ("muts", "woolly hat"), ("ijsje", "ice cream"), ("kampvuur", "campfire"), ("zeepbel", "soap bubble"),
    ("plas", "puddle"), ("regenboog", "rainbow"), ("sterren", "stars"), ("maan", "moon"),
    ("droom", "dream"), ("slapen", "to sleep"), ("wakker", "awake"), ("ontbijt", "breakfast"),
    ("pannenkoek", "pancake"), ("hagelslag", "chocolate sprinkles"), ("stroopwafel", "syrup waffle"),
    ("oliebol", "Dutch doughnut"), ("drop", "liquorice"), ("kaas", "cheese"), ("brood", "bread"),
    ("koffie", "coffee"), ("thee", "tea"), ("borrel", "drinks with friends"), ("uitwaaien", "a bracing walk in the wind"),
    ("polder", "reclaimed land"), ("dijk", "dyke"), ("gracht", "canal"), ("brug", "bridge"),
    ("molen", "windmill"), ("tulp", "tulip"), ("klomp", "wooden clog"), ("koning", "king"),
    ("feest", "party"), ("verjaardag", "birthday"), ("taart", "cake"), ("cadeau", "present"),
    ("vriend", "friend"), ("buurman", "neighbour"), ("knuffel", "hug"), ("lief", "sweet, kind"),
    ("blij", "happy"), ("moe", "tired"), ("rustig", "calm"), ("druk", "busy"), ("snel", "fast"),
    ("langzaam", "slow"), ("warm", "warm"), ("koud", "cold"), ("nat", "wet"), ("droog", "dry"),
    ("vandaag", "today"), ("morgen", "tomorrow"), ("gisteren", "yesterday"), ("weekend", "weekend"),
    ("werk", "work"), ("pauze", "break"), ("boek", "book"), ("schilderen", "to paint"),
    ("lezen", "to read"), ("zwemmen", "to swim"), ("springen", "to jump"), ("dansen", "to dance"),
    ("zwaaien", "to wave"), ("schat", "treasure, darling"), ("geluk", "luck, happiness"),
    ("doe maar gewoon", "just act normal"), ("lekker weertje", "lovely weather"),
    ("tot ziens", "goodbye"), ("dank je wel", "thank you"), ("alsjeblieft", "please / here you go"),
    ("goedemorgen", "good morning"), ("welterusten", "sleep well"), ("eet smakelijk", "enjoy your meal"),
]

COMPLIMENTS = [
    "You're doing great today!", "I'm glad you live here.", "You make this place cosy.",
    "Proud of you!", "You've got this.", "Your smile is the best.", "Remember to drink water!",
    "You deserve a nice break.", "Today's a good day for you.", "You're braver than you think.",
    "Thanks for visiting me!", "You're kind. That matters.", "Go easy on yourself today.",
    "You make me happy!", "Small steps still count.", "You light up the room.",
    "I believe in you!", "You're a great friend.", "Time for a little treat?",
    "You're clever AND kind.", "Hope your day is lekker!", "Big otter hug for you!",
    "You're my favourite human.", "Breathe in, breathe out.", "You've come so far!",
    "Something good is coming.", "Your ideas are brilliant.", "Rest is productive too.",
    "You're one of a kind.", "Keep being you!",
]

SCARF_COLOURS = {"red": (200, 50, 50), "blue": (60, 110, 200), "green": (60, 150, 80),
                 "yellow": (240, 200, 60), "purple": (150, 80, 200), "pink": (240, 120, 170),
                 "orange": (240, 140, 40)}
WALL_COLOURS = {"wood": (196, 150, 100), "blue": (120, 160, 210), "cream": (236, 224, 190),
                "pink": (230, 170, 180), "green": (150, 190, 140), "white": (235, 235, 235)}
ROOF_COLOURS = {"red": (170, 70, 56), "slate": (90, 96, 110), "green": (70, 120, 80),
                "blue": (60, 90, 150), "thatch": (190, 160, 90)}
DOOR_COLOURS = {"brown": (120, 72, 40), "red": (180, 50, 50), "blue": (50, 90, 170),
                "green": (50, 130, 80), "yellow": (220, 180, 50)}


def daily_pick(items, d, salt):
    return items[day_hash(d, salt) % len(items)]


def cycling_score(kind, wind, temp_c, rain_prob_2h):
    score = 10
    score -= {"drizzle": 4, "rain": 7, "storm": 9, "snow": 6, "fog": 1}.get(kind, 0)
    if rain_prob_2h >= 60:
        score -= 3
    elif rain_prob_2h >= 35:
        score -= 1
    wind = wind or 0
    score -= 5 if wind > 40 else 3 if wind > 30 else 1 if wind > 20 else 0
    if temp_c is not None:
        score -= 3 if temp_c < 0 else 2 if temp_c < 5 else 2 if temp_c > 30 else 0
    return max(0, min(10, score))


class Settings:
    """Choices made on the phone page, plus commands waiting for the otter."""

    def __init__(self, path):
        self.path = path
        self.lock = threading.Lock()
        self.data = {"name": "", "scarf": "red", "wall": "wood", "roof": "red", "door": "brown",
                     "postcards": [], "focus_until": None, "focus_minutes": 25}
        self.commands = []
        try:
            with open(path) as f:
                self.data.update(json.load(f))
        except FileNotFoundError:
            pass
        except Exception as e:
            print("[settings] couldn't read settings.json:", e)

    def _save(self):
        tmp = self.path + ".tmp"
        with open(tmp, "w") as f:
            json.dump(self.data, f, indent=1)
        os.replace(tmp, self.path)

    def snapshot(self):
        with self.lock:
            return json.loads(json.dumps(self.data))

    def update(self, **kw):
        with self.lock:
            self.data.update(kw)
            self._save()

    def push(self, cmd):
        with self.lock:
            self.commands.append(cmd)

    def pop_commands(self):
        with self.lock:
            cmds, self.commands = self.commands, []
        return cmds

    def add_postcard(self, place):
        place = " ".join(place.split())[:16]
        if not clean_text(place).strip():
            raise ValueError("Type the name of a place")
        with self.lock:
            self.data["postcards"] = (self.data["postcards"] +
                                      [{"id": uuid.uuid4().hex[:8], "place": place,
                                        "added": dt.date.today().isoformat()}])[-30:]
            self._save()
        self.push(("postcard", place))

    def remove_postcard(self, pid):
        with self.lock:
            self.data["postcards"] = [p for p in self.data["postcards"] if p["id"] != pid]
            self._save()

    def start_focus(self, minutes):
        minutes = max(5, min(120, minutes))
        self.update(focus_until=(dt.datetime.now() + dt.timedelta(minutes=minutes)).isoformat(),
                    focus_minutes=minutes)

    def stop_focus(self):
        self.update(focus_until=None)


# --------------------------------------------------------------------------
# Little web page for birthdays and messages
# --------------------------------------------------------------------------

MONTHS = ["January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December"]

PAGE_CSS = """
body{font-family:ui-monospace,Menlo,Consolas,monospace;background:#1f1a2e;color:#f4e8d0;
max-width:520px;margin:0 auto;padding:20px}
h1{color:#ffd27a;font-size:22px}
.card{background:#2c2540;border:3px solid #8a5a34;padding:14px;margin:14px 0}
input,select,button{font:inherit;padding:8px;border:2px solid #8a5a34;background:#f4e8d0;color:#2b1d14}
button{background:#ffd27a;cursor:pointer}
.row{display:flex;gap:8px;flex-wrap:wrap;margin:6px 0}
li{margin:8px 0;display:flex;justify-content:space-between;align-items:center;gap:8px}
.soon{color:#9fd8ff}.err{color:#ff8a8a}.small{font-size:13px;color:#b8aec8}
form.inline{display:inline}
"""


LIVE = {}          # latest info from the main loop, shown on the phone page


def _options(choices, current):
    return "".join(f"<option value='{k}'{' selected' if k == current else ''}>{k}</option>" for k in choices)


def render_page(book, board, settings, error=""):
    today = dt.date.today()
    cfg = settings.snapshot()
    name = cfg.get("name") or "the otter"
    rows = []
    for n, b, age in book.upcoming(today):
        when = "today!" if n == 0 else "tomorrow" if n == 1 else f"in {n} days"
        extra = f", turns {age}" if age else ""
        rows.append(
            f"<li><span>{html.escape(b['name'])} - {b['day']} {MONTHS[b['month']-1]}"
            f" <span class='soon'>({when}{extra})</span></span>"
            f"<form class='inline' method='post' action='/delete'>"
            f"<input type='hidden' name='id' value='{html.escape(b['id'])}'>"
            f"<button>remove</button></form></li>")
    cards = "".join(
        f"<li><span>{html.escape(p['place'])} <span class='small'>({html.escape(p['added'])})</span></span>"
        f"<form class='inline' method='post' action='/postcard-delete'>"
        f"<input type='hidden' name='id' value='{html.escape(p['id'])}'><button>remove</button></form></li>"
        for p in reversed(cfg.get("postcards", [])))
    months = "".join(f"<option value='{i+1}'>{m}</option>" for i, m in enumerate(MONTHS))
    err = f"<p class='err'>{html.escape(error)}</p>" if error else ""
    msg = board.current()
    showing = ""
    if msg:
        until = board.until.strftime("until %H:%M") if board.until else "until you clear it"
        showing = (f"<p>Showing now: <b>{html.escape(msg)}</b> <span class='small'>({until})</span> "
                   f"<form class='inline' method='post' action='/clear-message'>"
                   f"<button>clear</button></form></p>")
    word, meaning = daily_pick(WORDS, today, "word")
    focus = ""
    if cfg.get("focus_until"):
        left = dt.datetime.fromisoformat(cfg["focus_until"]) - dt.datetime.now()
        if left.total_seconds() > 0:
            focus = (f"<p>Focusing: <b>{int(left.total_seconds() // 60)} min</b> left. "
                     f"<form class='inline' method='post' action='/focus-stop'><button>stop</button></form></p>")
    rain = LIVE.get("rain_text") or "No rain expected in the next few hours."
    return f"""<!doctype html><html><head><meta charset='utf-8'>
<meta name='viewport' content='width=device-width,initial-scale=1'>
<title>Otter Pal</title><style>{PAGE_CSS}</style></head><body>
<h1>🦦 {html.escape(name.title() if cfg.get("name") else "Otter Pal")}</h1>{err}
<div class='card'><b>Today</b>
<p>🚲 Cycling weather: <b>{LIVE.get("bike_score") if LIVE.get("bike_score") is not None else "?"}/10</b></p>
<p>☔ {html.escape(rain)}</p>
<p>🇳🇱 Woord van de dag: <b>{html.escape(word)}</b> = {html.escape(meaning)}</p>
<p>💛 {html.escape(daily_pick(COMPLIMENTS, today, "kind"))}</p></div>
<div class='card'><b>Play</b>
<div class='row'><form class='inline' method='post' action='/throw'><input type='hidden' name='what' value='fish'>
<button>🐟 Throw a fish</button></form>
<form class='inline' method='post' action='/throw'><input type='hidden' name='what' value='ball'>
<button>🎾 Play fetch</button></form></div></div>
<div class='card'><b>Focus timer</b>{focus}
<form method='post' action='/focus'><div class='row'><select name='minutes'>
<option value='15'>15 minutes</option><option value='25' selected>25 minutes</option>
<option value='50'>50 minutes</option></select><button>Start</button></div></form>
<p class='small'>The otter works at its little desk while you do, then calls a break.</p></div>
<div class='card'><b>Send {html.escape(name)} a message</b>{showing}
<form method='post' action='/message'>
<div class='row'><input name='text' maxlength='60' placeholder='e.g. Have a lovely day!' required style='flex:1'></div>
<div class='row'><select name='minutes'>
<option value='30'>for 30 minutes</option><option value='120' selected>for 2 hours</option>
<option value='480'>for 8 hours</option><option value='1440'>for a day</option>
<option value='0'>until I clear it</option></select><button>Send</button></div></form>
<p class='small'>Letters, numbers and simple punctuation show on the screen. Emoji don't.</p></div>
<div class='card'><b>Postcards</b><p class='small'>Back from a trip? Pin a postcard on the otter's washing line.</p>
<form method='post' action='/postcard'><div class='row'>
<input name='place' maxlength='16' placeholder='e.g. Lisbon' required style='flex:1'><button>Pin it</button></div></form>
<ul>{cards or '<li>No postcards yet</li>'}</ul></div>
<div class='card'><b>Otter & house</b>
<form method='post' action='/settings'>
<div class='row'><input name='name' maxlength='10' placeholder='Otter name' value='{html.escape(cfg.get("name", ""))}'></div>
<div class='row'>Scarf <select name='scarf'>{_options(SCARF_COLOURS, cfg.get("scarf"))}</select></div>
<div class='row'>Walls <select name='wall'>{_options(WALL_COLOURS, cfg.get("wall"))}</select>
Roof <select name='roof'>{_options(ROOF_COLOURS, cfg.get("roof"))}</select>
Door <select name='door'>{_options(DOOR_COLOURS, cfg.get("door"))}</select></div>
<button>Save</button></form></div>
<div class='card'><b>Add a birthday</b>
<form method='post' action='/add'>
<div class='row'><input name='name' placeholder='Name' maxlength='30' required></div>
<div class='row'><input name='day' type='number' min='1' max='31' placeholder='Day' required style='width:5em'>
<select name='month'>{months}</select>
<input name='year' type='number' min='1900' placeholder='Year (optional)' style='width:9em'></div>
<button>Add</button></form></div>
<div class='card'><b>Coming up</b><ul>{''.join(rows) or '<li>No birthdays yet</li>'}</ul></div>
</body></html>"""


def make_handler(book, board, settings):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_GET(self):
            u = urllib.parse.urlparse(self.path)
            if u.path != "/":
                self.send_error(404)
                return
            error = urllib.parse.parse_qs(u.query).get("error", [""])[0]
            body = render_page(book, board, settings, error).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def do_POST(self):
            length = min(int(self.headers.get("Content-Length", 0)), 10_000)
            form = urllib.parse.parse_qs(self.rfile.read(length).decode("utf-8"))
            get = lambda k: form.get(k, [""])[0].strip()  # noqa: E731
            error = ""
            try:
                if self.path == "/add":
                    year = int(get("year")) if get("year") else None
                    book.add(get("name"), int(get("month")), int(get("day")), year)
                elif self.path == "/delete":
                    book.remove(get("id"))
                elif self.path == "/message":
                    board.set(get("text"), int(get("minutes") or 0))
                elif self.path == "/clear-message":
                    board.clear()
                elif self.path == "/throw":
                    settings.push(("throw", "ball" if get("what") == "ball" else "fish"))
                elif self.path == "/focus":
                    settings.start_focus(int(get("minutes") or 25))
                elif self.path == "/focus-stop":
                    settings.stop_focus()
                elif self.path == "/postcard":
                    settings.add_postcard(get("place"))
                elif self.path == "/postcard-delete":
                    settings.remove_postcard(get("id"))
                elif self.path == "/settings":
                    pick = lambda k, table, default: get(k) if get(k) in table else default  # noqa: E731
                    settings.update(name=" ".join(get("name").split())[:10],
                                    scarf=pick("scarf", SCARF_COLOURS, "red"),
                                    wall=pick("wall", WALL_COLOURS, "wood"),
                                    roof=pick("roof", ROOF_COLOURS, "red"),
                                    door=pick("door", DOOR_COLOURS, "brown"))
            except ValueError as e:
                error = str(e) if "invalid literal" not in str(e) else "Please check the date"
            self.send_response(303)
            self.send_header("Location", "/" + ("?error=" + urllib.parse.quote(error) if error else ""))
            self.end_headers()
    return Handler


def start_web_server(book, board, settings, port):
    try:
        srv = ThreadingHTTPServer(("0.0.0.0", port), make_handler(book, board, settings))
    except OSError as e:
        print(f"[web] couldn't start the web page on port {port}: {e}")
        return
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    print(f"[web] page running on port {port}")


# --------------------------------------------------------------------------
# 3x5 pixel font
# --------------------------------------------------------------------------

_G = {
    "0": "111101101101111", "1": "010110010010111", "2": "111001111100111",
    "3": "111001111001111", "4": "101101111001001", "5": "111100111001111",
    "6": "111100111101111", "7": "111001001001001", "8": "111101111101111",
    "9": "111101111001111", "A": "010101111101101", "B": "110101110101110",
    "C": "011100100100011", "D": "110101101101110", "E": "111100110100111",
    "F": "111100110100100", "G": "011100101101011", "H": "101101111101101",
    "I": "111010010010111", "J": "001001001101010", "K": "101101110101101",
    "L": "100100100100111", "M": "101111111101101", "N": "110101101101101",
    "O": "010101101101010", "P": "110101110100100", "Q": "010101101110011",
    "R": "110101110101101", "S": "011100010001110", "T": "111010010010010",
    "U": "101101101101111", "V": "101101101101010", "W": "101101101111101",
    "X": "101101010101101", "Y": "101101010010010", "Z": "111001010100111",
    " ": "000000000000000", ":": "000010000010000", "!": "010010010000010",
    ".": "000000000000010", ",": "000000000010100", "'": "010010000000000",
    "-": "000000111000000", "/": "001001010100100", "?": "111001010000010",
    "°": "010101010000000", "+": "000010111010000", "&": "010101010101011",
    "(": "010100100100010", ")": "010001001001010", '"': "101101000000000",
    ";": "000010000010100", "*": "000101010101000", "#": "101111101111101",
    "<": "001010100010001", ">": "100010001010100", "=": "000111000111000",
    "%": "101001010100101", "_": "000000000000111", "@": "111101111100011",
}
FONT = {k: [v[i:i + 3] for i in range(0, 15, 3)] for k, v in _G.items()}


def clean_text(s):
    out = []
    for ch in s.upper():
        if ch in FONT:
            out.append(ch)
        else:
            base = unicodedata.normalize("NFKD", ch).encode("ascii", "ignore").decode()
            out.append(base if base in FONT else ("" if not base else "?"))
    return "".join(out)


def text_width(s, scale=1):
    return max(0, len(clean_text(s)) * 4 * scale - scale)


def draw_text(surf, s, x, y, color, scale=1, shadow=None):
    s = clean_text(s)
    if shadow:
        draw_text(surf, s, x + scale, y + scale, shadow, scale)
    for ch in s:
        for ry, row in enumerate(FONT[ch]):
            for rx, bit in enumerate(row):
                if bit == "1":
                    surf.fill(color, (x + rx * scale, y + ry * scale, scale, scale))
        x += 4 * scale


def wrap_text(s, width):
    words, lines, line = clean_text(s).split(), [], ""
    for w in words:
        while len(w) > width:
            if line:
                lines.append(line)
                line = ""
            lines.append(w[:width])
            w = w[width:]
        if not line:
            line = w
        elif len(line) + 1 + len(w) <= width:
            line += " " + w
        else:
            lines.append(line)
            line = w
    if line:
        lines.append(line)
    return lines




# --------------------------------------------------------------------------
# Hi-res canvas: the world is laid out in 200x120 "world pixels", but drawn
# HI_S times finer, so curves, lines and sprites get more detail.
# --------------------------------------------------------------------------

HI_S = 4            # screen pixels per world pixel on the drawing canvas (set at start-up)


class HiCanvas:
    """A surface that takes world coordinates and draws them HI_S times finer."""
    _cache = {}
    _order = []

    def __init__(self, surf, scale=None):
        self.surf = surf
        self.S = scale or HI_S

    # -- sizes are reported in world pixels
    def get_size(self):
        w, h = self.surf.get_size()
        return w // self.S, h // self.S

    def get_width(self):
        return self.get_size()[0]

    def get_height(self):
        return self.get_size()[1]

    def _r(self, rect):
        x, y, w, h = rect if len(rect) == 4 else (*rect[0], *rect[1])
        S = self.S
        x0, y0 = int(round(x * S)), int(round(y * S))
        return pygame.Rect(x0, y0, max(1, int(round((x + w) * S)) - x0), max(1, int(round((y + h) * S)) - y0))

    def fill(self, col, rect=None):
        if rect is None:
            self.surf.fill(col)
        else:
            self.surf.fill(col, self._r(rect))

    def set_at(self, pos, col):
        S = self.S
        self.surf.fill(col, (int(pos[0] * S), int(pos[1] * S), S, S))

    def get_at(self, pos):
        return self.surf.get_at((int(pos[0] * self.S), int(pos[1] * self.S)))

    def blit(self, src, pos):
        S = self.S
        dest = (int(round(pos[0] * S)), int(round(pos[1] * S)))
        if isinstance(src, HiCanvas):
            self.surf.blit(src.surf, dest)
            return
        key = id(src)
        hit = HiCanvas._cache.get(key)
        if hit is None or hit[0] is not src or hit[2] != S:
            w, h = src.get_size()
            hit = (src, pygame.transform.scale(src, (w * S, h * S)), S)
            HiCanvas._cache[key] = hit
            HiCanvas._order.append(key)
            if len(HiCanvas._order) > 48:
                HiCanvas._cache.pop(HiCanvas._order.pop(0), None)
        scaled = hit[1]
        scaled.set_alpha(src.get_alpha())
        self.surf.blit(scaled, dest)

    def set_clip(self, rect):
        self.surf.set_clip(None if rect is None else self._r(rect))

    def set_alpha(self, a):
        self.surf.set_alpha(a)

    def get_alpha(self):
        return self.surf.get_alpha()

    def copy(self):
        return HiCanvas(self.surf.copy(), self.S)

    def subsurface(self, rect):
        return HiCanvas(self.surf.subsurface(self._r(rect)), self.S)


def new_canvas(w, h, alpha=False):
    flags = pygame.SRCALPHA if alpha else 0
    return HiCanvas(pygame.Surface((w * HI_S, h * HI_S), flags), HI_S)


class _HiDraw:
    """pygame.draw, but taking world coordinates on a HiCanvas."""

    @staticmethod
    def _p(surf, pt):
        S = surf.S
        return (pt[0] * S + S // 2, pt[1] * S + S // 2)

    @staticmethod
    def _w(surf, width):
        return 0 if width == 0 else max(1, int(round(width * surf.S * 0.5)))

    def circle(self, surf, col, center, r, width=0):
        if not isinstance(surf, HiCanvas):
            return pygame.draw.circle(surf, col, center, r, width)
        pygame.draw.circle(surf.surf, col, self._p(surf, center), max(1, r * surf.S), self._w(surf, width))

    def ellipse(self, surf, col, rect, width=0):
        if not isinstance(surf, HiCanvas):
            return pygame.draw.ellipse(surf, col, rect, width)
        pygame.draw.ellipse(surf.surf, col, surf._r(rect), self._w(surf, width))

    def line(self, surf, col, a, b, width=1):
        if not isinstance(surf, HiCanvas):
            return pygame.draw.line(surf, col, a, b, width)
        pygame.draw.line(surf.surf, col, self._p(surf, a), self._p(surf, b), self._w(surf, width))

    def lines(self, surf, col, closed, pts, width=1):
        if not isinstance(surf, HiCanvas):
            return pygame.draw.lines(surf, col, closed, pts, width)
        pygame.draw.lines(surf.surf, col, closed, [self._p(surf, q) for q in pts], self._w(surf, width))

    def polygon(self, surf, col, pts, width=0):
        if not isinstance(surf, HiCanvas):
            return pygame.draw.polygon(surf, col, pts, width)
        pygame.draw.polygon(surf.surf, col, [self._p(surf, q) for q in pts], self._w(surf, width))


pd = _HiDraw()


def hscale(spr, size):
    w, h = size
    S = spr.S
    return HiCanvas(pygame.transform.scale(spr.surf, (max(1, w * S), max(1, h * S))), S)


def hrotate(spr, angle):
    return HiCanvas(pygame.transform.rotate(spr.surf, angle), spr.S)


def hflip(spr):
    return HiCanvas(pygame.transform.flip(spr.surf, True, False), spr.S)


def scale2x(grid):
    """The classic Scale2x pixel-art upscaler: doubles the pixels and smooths the diagonals."""
    h, w = len(grid), len(grid[0])
    out = [[None] * (w * 2) for _ in range(h * 2)]
    for y in range(h):
        for x in range(w):
            p = grid[y][x]
            a = grid[y - 1][x] if y > 0 else p
            b = grid[y][x + 1] if x < w - 1 else p
            c = grid[y][x - 1] if x > 0 else p
            d = grid[y + 1][x] if y < h - 1 else p
            e0 = e1 = e2 = e3 = p
            if c == a and c != d and a != b:
                e0 = a
            if a == b and a != c and b != d:
                e1 = b
            if d == c and d != b and c != a:
                e2 = c
            if b == d and b != a and d != c:
                e3 = d
            out[2 * y][2 * x], out[2 * y][2 * x + 1] = e0, e1
            out[2 * y + 1][2 * x], out[2 * y + 1][2 * x + 1] = e2, e3
    return out


# --------------------------------------------------------------------------
# Sprites
# --------------------------------------------------------------------------

def render_grid(grid, palette, px):
    h, w = len(grid), len(grid[0])
    surf = pygame.Surface((w * px, h * px), pygame.SRCALPHA)
    for y, row in enumerate(grid):
        for x, ch in enumerate(row):
            if ch != ".":
                surf.fill(palette[ch], (x * px, y * px, px, px))
    return surf


def make_sprite(rows, palette, scale=1, smooth=True):
    """Build a sprite on the hi-res canvas; Scale2x adds detail where the resolution allows."""
    for y, row in enumerate(rows):
        assert len(row) == len(rows[0]), (y, row)
    grid = [list(r) for r in rows]
    px = scale * HI_S
    if smooth and px % 2 == 0 and px >= 2:
        grid, px = scale2x(grid), px // 2
    return HiCanvas(render_grid(grid, palette, px), HI_S)


PALETTE = {
    "K": (43, 29, 20), "D": (94, 58, 31), "B": (138, 90, 52),
    "C": (232, 207, 160), "E": (20, 16, 14), "W": (255, 255, 255),
    "N": (58, 36, 24), "P": (224, 138, 122),
}

_OTTER = [
    "................",
    "...KK......KK...",
    "..KDBK....KBDK..",
    "..KBBBKKKKBBBK..",
    ".KBBBBBBBBBBBBK.",
    ".KBBCCCBBCCCBBK.",
    "KBBCCWCCCCWCCBBK",
    "KBCCCECNNCECCCBK",
    "KBCPCCCCCCCCPCBK",
    ".KBCCCCCCCCCCBK.",
    "..KBBCCCCCCBBK..",
    ".KBBBCCCCCCBBBK.",
    "KBBKBCCCCCCBKBBK",
    "KBBKBCCCCCCBKBBK",
    ".KBBBBBBBBBBBBK.",
    "..KKKK....KKKK..",
]
OTTER_FRAMES = {
    "open":  {},
    "blink": {6: "KBBCCCCCCCCCCBBK", 7: "KBCCCKCNNCKCCCBK"},
    "sleep": {6: "KBBCCCCCCCCCCBBK", 7: "KBCCKKCNNCKKCCBK"},
    "happy": {6: "KBBCCKCCCCKCCBBK", 7: "KBCCKCKNNKCKCCBK"},
    "yawn":  {6: "KBBCCCCCCCCCCBBK", 7: "KBCCKKCNNCKKCCBK",
              8: "KBCPCCCKKCCCPCBK", 9: ".KBCCCKPPKCCCBK.", 10: "..KBBCCKKCCBBK.."},
}


OTTER_HI_PAL = dict(PALETTE, L=(170, 118, 74), D=(102, 64, 36), c=(212, 184, 136),
                    n=(150, 112, 100), w=(96, 64, 42), p=(176, 112, 96), s=(255, 255, 255))


def otter_frame(name):
    """The otter at double detail: Scale2x of the classic sprite, then hand-made touches."""
    rows = [r.replace("D", "p") for r in _OTTER]          # inner ears go pinkish
    for i, row in OTTER_FRAMES[name].items():
        rows[i] = row
    g = scale2x([list(r) for r in rows])                  # 32 x 32
    ears = ["......KKKK............KKKK......",              # small, round otter ears
            ".....KLLBBK..........KLLBBK.....",
            "....KLppBBK..........KLBppBK....",
            "....KBppBBBKK......KKBBBppBK...."]
    for i, row in enumerate(ears):
        assert len(row) == 32
        g[2 + i] = list(row)
    out = [row[:] for row in g]

    def at(y, x):
        return g[y][x] if 0 <= y < 32 and 0 <= x < 32 else "."

    for y in range(32):                                   # fur shading, light from the top left
        for x in range(32):
            ch = g[y][x]
            if ch == "B":
                if at(y, x + 1) == "K" or at(y + 1, x) == "K":
                    out[y][x] = "D"
                elif (at(y - 1, x) == "K" or at(y, x - 1) == "K") and y < 14:
                    out[y][x] = "L"
            elif ch == "C":
                if at(y, x + 1) in "BK" or at(y + 1, x) in "BK":
                    out[y][x] = "c"
    if name == "open":                                    # round eyes with a sparkle
        for ex in (10, 20):
            for yy in range(12, 16):
                out[yy][ex] = out[yy][ex + 1] = "E"
            out[12][ex] = "s"
            out[13][ex + 1] = "E"
    if name in ("open", "blink", "happy"):                # little "w" mouth
        out[16][15] = out[16][16] = "K"
        out[17][14] = out[17][17] = "K"
    for (yy, xx) in ((14, 15), (14, 16)):                 # shiny nose
        if out[yy][xx] == "N":
            out[yy][xx] = "n" if xx == 15 else "N"
    for (yy, xx) in ((16, 3), (16, 4), (18, 4), (18, 5)):  # whiskers
        for X in (xx, 31 - xx):
            if out[yy][X] not in "K.":
                out[yy][X] = "w"
    for (yy, xx) in ((24, 13), (26, 17), (23, 18), (27, 12)):   # fluffy tummy
        if out[yy][xx] == "C":
            out[yy][xx] = "c"
    for xx in (6, 9, 22, 25):                             # toes
        if out[29][xx] in "BDL":
            out[29][xx] = "D"
    return HiCanvas(render_grid(out, OTTER_HI_PAL, HI_S), HI_S)


# otter floating on its back, side view (drawn at 2x)
FLOAT_ROWS = [
    "..KK" + "." * 20,
    ".KBBK.......KK....KK....",
    "KBBBBK.....KCCK..KBBK...",
    "KBWEBBKKKKKCCCKKKKBBK.KK",
    "KBBBBBCCCCCCCCCCCCCCBKBK",
    "NCCCBBCCCCCCCCCCCCCCBBBK",
    ".KCC" + "B" * 18 + "K.",
    "..KKK" + "B" * 15 + "KK..",
    "....." + "K" * 15 + "....",
]

DUCK_PAL = {"G": (40, 110, 60), "E": (10, 10, 10), "Y": (240, 160, 40), "W": (240, 240, 230),
            "B": (170, 140, 110), "D": (120, 90, 60), "T": (90, 80, 70),
            "y": (250, 220, 80), "o": (240, 140, 40)}
DUCK_ROWS = [
    ".....GG..",
    "....GGEGY",
    ".....GG..",
    "T...WWW..",
    "TBBBBBBB.",
    ".BBDDDBB.",
    "..BBBBB..",
]
DUCKLING_ROWS = ["..yy.", "..yEo", "yyyy.", ".yyy."]

PUMPKIN_PAL = {"g": (90, 110, 40), "o": (200, 100, 20), "O": (240, 140, 40), "F": (110, 50, 10)}
PUMPKIN_ROWS = [
    "....gg....",
    "..oOOoOo..",
    ".oOOOoOOo.",
    "oOFFoOFFOo",
    "oOOOoOOOOo",
    "oOFOFOFOOo",
    ".oOFFFFOo.",
    "..oooooo..",
]

HERON_PAL = {"g": (150, 155, 165), "W": (235, 235, 240), "E": (20, 20, 20), "y": (230, 180, 60),
             "d": (90, 95, 110), "l": (200, 170, 90)}
HERON_ROWS = [
    "...gg......",
    "..gWWg.....",
    "yyWEWg.....",
    "...gWg.....",
    "....Wg.....",
    "....Wg.....",
    "....gW.....",
    "....gWgg...",
    "...gggggg..",
    "..ggddgggg.",
    ".gggddggggg",
    "..ggggggg..",
    "....gg.....",
    ".....l.l...",
    ".....l.l...",
    ".....l.l...",
    ".....l.l...",
    "....ll.ll..",
]
DREAMS = {
    "fish":   ((120, 170, 200), [".111.1", "111111", ".111.1"]),
    "star":   ((255, 220, 90), ["..1..", "11111", ".111.", "1...1"]),
    "heart":  ((255, 100, 130), [".1.1.", "11111", "11111", ".111.", "..1.."]),
    "moon":   ((240, 236, 200), [".11", "11.", "11.", ".11"]),
    "pebble": ((160, 160, 170), [".111.", "11111", ".111."]),
    "kite":   ((240, 90, 90), ["..1..", ".111.", "11111", ".111.", "..1.."]),
}
TRICKS = ["wave", "spin", "juggle", "handstand", "backflip"]

BAT = [["1.....1", "11.1.11", "..111.."], ["...1...", ".11111.", "1..1..1"]]
HEART = ["01010", "11111", "11111", "01110", "00100"]

# Little pixel flowers: 'a' = petal colour, 'b' = centre colour
FLOWER_HEADS = {
    "daisy": [".a.", "aba", ".a."],
    "tulip": ["a.a", "aaa", ".a."],
    "poppy": ["aaa", "aba", "aaa"],
    "bell":  [".a.", "aaa", "a.a"],
}
FLOWER_COLOURS = {
    "daisy": [((255, 255, 255), (255, 210, 70))],
    "tulip": [((235, 60, 70), None), ((255, 200, 60), None), ((240, 120, 180), None),
              ((160, 90, 210), None)],
    "poppy": [((230, 70, 50), (40, 20, 20)), ((255, 150, 60), (90, 50, 20))],
    "bell":  [((120, 150, 240), None), ((190, 160, 250), None)],
}

WINTER_BRANCHES = [((15, 64), (5, 52)), ((15, 62), (25, 49)), ((15, 63), (15, 44)),
                   ((10, 57), (3, 55)), ((21, 55), (29, 53)), ((15, 50), (10, 45)),
                   ((15, 50), (20, 44))]
XMAS_LIGHTS = sorted({(round(a[0] + (b[0] - a[0]) * f), round(a[1] + (b[1] - a[1]) * f))
                      for a, b in WINTER_BRANCHES for f in (0.4, 0.75, 1.0)})
XMAS_COLOURS = [(255, 70, 70), (90, 230, 110), (255, 220, 80), (110, 170, 255)]

SKY = {
    "day":        [(98, 166, 232), (118, 180, 238), (140, 195, 242), (166, 210, 246)],
    "dawn":       [(70, 66, 128), (146, 96, 140), (230, 140, 110), (250, 196, 130)],
    "night":      [(14, 18, 44), (20, 26, 60), (28, 36, 78), (38, 48, 96)],
    "grey_day":   [(112, 124, 140), (126, 138, 152), (142, 152, 164), (160, 168, 178)],
    "grey_night": [(22, 24, 32), (28, 30, 40), (34, 37, 48), (42, 45, 56)],
}
TINT = {
    ("night", False): (8, 12, 40, 130), ("night", True): (5, 6, 12, 150),
    ("dawn", False): (90, 40, 60, 50), ("dawn", True): (30, 30, 44, 70),
    ("day", False): None, ("day", True): (30, 34, 44, 40),
}
GRASS = {"spring": (104, 176, 84), "summer": (98, 170, 82),
         "autumn": (128, 158, 74), "winter": (118, 146, 102)}
CONFETTI = [(255, 90, 110), (255, 210, 90), (110, 200, 255), (150, 240, 140), (220, 140, 255)]
WATER = (66, 128, 198)

# temperatures (°C) for the otter's choices
SWIM_C, SUNGLASSES_C, SCARF_C, BEANIE_C, BUTTERFLY_C = 18, 22, 8, 3, 12
HEATWAVE_C = 27
# wind (km/h) for the otter's choices
KITE_KMH, CALM_KMH, BIKE_MAX_KMH = 25, 12, 25
CHIMNEY = (66, 45)


# --------------------------------------------------------------------------
# The world
# --------------------------------------------------------------------------

class World:
    def __init__(self, state=None):
        self.state = state or OtterState(STATE_PATH, persist=False)
        rnd = random.Random(7)
        self.sprites = {k: otter_frame(k) for k in OTTER_FRAMES}
        self.float_sprite = make_sprite(FLOAT_ROWS, PALETTE, 2)
        self.pup_sprite = hscale(otter_frame("happy"), (18, 18))
        self.heron_sprite = make_sprite(HERON_ROWS, HERON_PAL, 2)
        duck = make_sprite(DUCK_ROWS, DUCK_PAL)
        self.duck = {1: duck, -1: hflip(duck)}
        dl = make_sprite(DUCKLING_ROWS, DUCK_PAL)
        self.duckling = {1: dl, -1: hflip(dl)}
        self.pumpkin = make_sprite(PUMPKIN_ROWS, PUMPKIN_PAL, 2)
        face = [''.join(ch if ch == "F" else "." for ch in row) for row in PUMPKIN_ROWS]
        self.pumpkin_glow = make_sprite(face, {"F": (255, 226, 90)}, 2)
        self.all_flowers = self._make_flowers(rnd)
        self.lands, self.flower_cache = {}, {}
        self.sky_cache, self.overlay_cache = {}, {}
        self.rainbow = self._make_rainbow()
        self.stars = [(rnd.randrange(W), rnd.randrange(2, 54), rnd.randrange(40)) for _ in range(45)]
        self.clouds = [[rnd.uniform(-20, W), rnd.uniform(6, 30), rnd.uniform(0.04, 0.12),
                        rnd.choice((0.8, 1.0, 1.3))] for _ in range(6)]
        self.butterflies = [(rnd.uniform(40, 100), rnd.uniform(0, 6.28),
                             rnd.choice([(255, 200, 60), (255, 255, 255), (250, 140, 200), (120, 190, 255)]))
                            for _ in range(3)]
        self.bats = [(rnd.uniform(0, 6.28), rnd.uniform(0.7, 1.2)) for _ in range(3)]
        self.fog = pygame.Surface((W, 8), pygame.SRCALPHA)
        self.fog.fill((220, 224, 230, 80))

        # the otter
        self.x, self.target, self.next_move = 60.0, 60.0, 0.0
        self.moving = False
        self.next_blink = self.blink_until = self.happy_until = 0.0
        self.sleeping, self.prev_sleeping = False, None
        self.wake_until = self.bedtime_until = 0.0
        self.yawn_until, self.next_yawn = 0.0, 0.0
        self.mode, self.swim_until, self.swim_x = "land", 0.0, 155.0
        self.last_message = None

        # weather & friends
        self.drops, self.splashes, self.ripples, self.jumps = [], [], [], []
        self.flakes, self.confetti, self.zs, self.hearts = [], [], [], []
        self.leaves, self.fireflies, self.rockets, self.sparks = [], [], [], []
        self.season = None
        self.duck_x, self.duck_dir = 175.0, -1
        self.prev_kind, self.rainbow_start, self.rainbow_until = None, 0.0, 0.0
        self.fog_x, self.flash, self.bolt, self.tick = 0.0, 0, None, 0
        self.umbrella = None

        # batch 1: home, activities and weather fun
        self.inside = False
        self.activity, self.act_until, self.act_step = None, 0.0, 0
        self.hobby_kind, self.painting = "book", []
        self.jump_t, self.in_pile_until = -10.0, 0.0
        self.puddle_until, self.puddle_since = 0.0, 0.0
        self.bubbles, self.smoke, self.embers = [], [], []
        self.snow_since = None
        self.find_msg, self.find_until = None, 0.0
        self.speech_q = []
        self.otter_bday, self.otter_age, self.garden = False, 1, 0
        self.pups_on, self.lucky = False, False
        self.snail_visible = False

        # batch 2: phone features
        self.thrown = None
        self.ball = None
        self.burst_until = 0.0
        self.afternoon_said = None

        # batch 3: camera
        self.look_x, self.look_t, self.last_greet = 0.0, -100.0, -100.0
        self._win_before = self._win_after = None
        self.hiding, self.highfive_until = False, 0.0
        self.dancing, self.notes = False, []
        self.kite_on = False
        self.tulip_cache = {}

        # batch 1, part 2: friends, garden, sky and special days
        self.trick, self.trick_t = "wave", 0.0
        self.birds = [[18, 47, 0.0], [8, 56, 0.0], [26, 55, 0.0]]
        self.heron = None                    # dict while a heron is visiting
        self.next_heron = 0.0
        self.frog = None
        self.snail_x = 150.0
        self.geese = None
        self.next_geese = 0.0
        self.pups = [40.0, 30.0]
        self.shooting = []
        self.aurora_surf, self.aurora_t = None, -10.0
        self.leap = None
        self.next_leap = 0.0
        self.golden_given = None
        self.golden_until = 0.0

    # ---------- static pieces ----------
    def _land(self, season):
        if season not in self.lands:
            self.lands[season] = self._make_land(random.Random(7), season)
        return self.lands[season]

    def _make_land(self, rnd, season):
        s = new_canvas(W, H, alpha=True)
        pd.ellipse(s, (78, 128, 96), (-30, 58, 120, 50))
        pd.ellipse(s, (78, 128, 96), (110, 54, 130, 56))
        pd.ellipse(s, (70, 140, 78), (40, 66, 130, 44))
        g = GRASS[season]
        s.fill(g, (0, GRASS_Y, W, H - GRASS_Y))
        s.fill(tuple(min(255, v + 30) for v in g), (0, GRASS_Y, W, 1))
        for _ in range(60):
            x, y = rnd.randrange(W), rnd.randrange(GRASS_Y + 3, H)
            s.fill(tuple(max(0, v - 20) for v in g), (x, y, 1, 2))
        # tree
        s.fill((96, 64, 40), (12, 62, 6, 28))
        s.fill((70, 46, 28), (12, 62, 2, 28))
        if season == "winter":
            for a, b in WINTER_BRANCHES:
                pd.line(s, (84, 58, 40), a, b)
        else:
            dark, light = {"spring": ((56, 128, 70), (80, 152, 84)),
                           "summer": ((48, 118, 64), (72, 146, 80)),
                           "autumn": ((196, 104, 36), (232, 160, 60))}[season]
            for cx, cy, r in ((15, 54, 11), (6, 61, 7), (24, 61, 7)):
                pd.circle(s, dark, (cx, cy), r)
            for cx, cy, r in ((13, 50, 5), (5, 58, 3), (22, 57, 3)):
                pd.circle(s, light, (cx, cy), r)
            dots = {"spring": [(250, 190, 214), (255, 235, 244)],
                    "autumn": [(190, 60, 40), (240, 200, 80)]}.get(season)
            if dots:
                for _ in range(30):
                    a, r = rnd.uniform(0, 6.28), rnd.uniform(0, 10)
                    s.set_at((int(15 + math.cos(a) * r), int(54 + math.sin(a) * r)), rnd.choice(dots))
            if season == "autumn":                 # fallen leaves
                for _ in range(24):
                    s.set_at((rnd.randrange(0, 40), rnd.randrange(GRASS_Y + 1, GRASS_Y + 8)),
                             rnd.choice([(214, 110, 40), (230, 170, 60), (190, 60, 40)]))
        # pond
        pd.ellipse(s, (46, 96, 160), (124, 94, 90, 24))
        pd.ellipse(s, WATER, (127, 96, 84, 20))
        # reeds
        for x, hgt in ((123, 14), (126, 19), (129, 12), (132, 16)):
            pd.line(s, (60, 120, 60) if season != "winter" else (130, 120, 80),
                             (x, 100), (x, 100 - hgt))
            s.fill((120, 80, 40), (x, 100 - hgt, 2, 4))
        if season in ("spring", "summer"):
            for _ in range(16):
                x, y = rnd.randrange(30, 118), rnd.randrange(GRASS_Y + 4, H - 2)
                s.set_at((x, y), rnd.choice([(255, 240, 120), (255, 160, 190), (255, 255, 255)]))
        if s.S >= 2:
            self._add_texture(s, rnd, season)
        return s

    def _add_texture(self, s, rnd, season):
        """Fine detail only possible on the hi-res canvas: grass blades, leafy clumps, hill speckles."""
        S, surf = s.S, s.surf
        g = GRASS[season]
        dark = tuple(max(0, v - 26) for v in g)
        light = tuple(min(255, v + 22) for v in g)
        for _ in range(700):                                   # grass blades
            x = rnd.randrange(0, W * S)
            y = rnd.randrange((GRASS_Y + 2) * S, H * S)
            if surf.get_at((x, y))[:3] != g:
                continue                                       # not on plain grass (pond, garden...)
            h = rnd.randint(S // 2 + 1, S + 1)
            pygame.draw.line(surf, rnd.choice((dark, dark, light)), (x, y), (x + rnd.choice((-1, 0, 0, 1)), y - h))
        for _ in range(260):                                   # speckles on the hills
            x, y = rnd.randrange(0, W * S), rnd.randrange(56 * S, GRASS_Y * S)
            col = surf.get_at((x, y))
            if col.a and col[:3] in ((78, 128, 96), (70, 140, 78)):
                shade = rnd.choice((-12, 10))
                surf.set_at((x, y), tuple(max(0, min(255, v + shade)) for v in col[:3]))
        if season != "winter":                                 # leafy clumps in the tree
            canopy = {"spring": ((56, 128, 70), (88, 160, 92)), "summer": ((40, 104, 56), (80, 152, 86)),
                      "autumn": ((176, 90, 30), (240, 176, 76))}[season]
            for _ in range(70):
                a, r = rnd.uniform(0, 6.28), rnd.uniform(0, 10)
                cx, cy = 15 + math.cos(a) * r, 54 + math.sin(a) * r
                hx, hy = int(cx * S), int(cy * S)
                if surf.get_at((hx, hy)).a:
                    col = canopy[1] if cy < 53 and rnd.random() < 0.6 else canopy[0]
                    pygame.draw.circle(surf, col, (hx, hy), rnd.randint(S // 2, S))

    def _make_flowers(self, rnd):
        def flower(x, y):
            kind = rnd.choice(list(FLOWER_HEADS))
            petal, centre = rnd.choice(FLOWER_COLOURS[kind])
            return (x, y, kind, petal, centre, rnd.randrange(3, 7), rnd.uniform(0, 6.28))

        back, front = [], []
        for x in (4, 9, 21, 27):
            back.append(flower(x + rnd.randrange(-1, 2), GRASS_Y + rnd.randrange(2, 5)))
        for x in range(34, 118, 9):
            back.append(flower(x + rnd.randrange(-3, 4), GRASS_Y + rnd.randrange(3, 8)))
        for x in range(6, 124, 13):
            front.append(flower(x + rnd.randrange(-3, 4), H - 11 + rnd.randrange(-2, 2)))
        for x in (138, 150, 186, 196):
            back.append(flower(x, 95 + rnd.randrange(-1, 1)))
        back.sort(key=lambda f: f[1])
        front.sort(key=lambda f: f[1])
        return back, front

    def _flowers(self, season):
        """Full meadow in spring & summer, a few left in autumn, none in winter."""
        if season not in self.flower_cache:
            back, front = self.all_flowers
            if season == "autumn":
                back, front = back[::3], front[::3]
            elif season == "winter":
                back, front = [], []
            self.flower_cache[season] = (back, front)
        return self.flower_cache[season]

    def _make_rainbow(self):
        if HI_S > 1:                                   # smooth arcs at full detail
            s = new_canvas(W, H, alpha=True)
            cols = [(230, 60, 60), (245, 150, 50), (245, 225, 70), (90, 190, 90), (70, 130, 230), (140, 90, 200)]
            for i, col in enumerate(cols):
                pd.circle(s, (*col, 170), (110, 104), 76 - i * 2, 4)
            s.surf.fill((0, 0, 0, 0), (0, 104 * HI_S, W * HI_S, (H - 104) * HI_S))
            return s
        s = pygame.Surface((W, H), pygame.SRCALPHA)
        cols = [(230, 60, 60), (245, 150, 50), (245, 225, 70), (90, 190, 90), (70, 130, 230), (140, 90, 200)]
        cx, cy = 110, 104
        for y in range(cy):
            for x in range(W):
                i = int((76 - math.hypot(x - cx, y - cy)) // 2)
                if 0 <= i < 6:
                    s.set_at((x, y), (*cols[i], 170))
        return s

    def _sky(self, key):
        if key not in self.sky_cache:
            cols = SKY[key]
            s = pygame.Surface((W, H))
            for i, col in enumerate(cols):
                s.fill(col, (0, i * 22, W, H - i * 22))
            for i in range(1, len(cols)):
                y = i * 22
                for x in range(W):
                    if x % 2 == 0:
                        s.set_at((x, y - 1), cols[i])
                    if x % 4 == 0:
                        s.set_at((x, y - 2), cols[i])
            self.sky_cache[key] = s
        return self.sky_cache[key]

    def _overlay(self, rgba, size=(W, H)):
        key = (rgba, size)
        if key not in self.overlay_cache:
            o = pygame.Surface(size, pygame.SRCALPHA)
            o.fill(rgba)
            self.overlay_cache[key] = o
        return self.overlay_cache[key]

    # ---------- interaction ----------
    def poke(self, t):
        if self.sleeping:
            self.zs.append([WINDOW[0] + 8, WINDOW[1] - 2, 0])
        else:
            self.happy_until = t + 4
            if self.lucky and self.golden_given != dt.date.today():
                self.golden_given = dt.date.today()
                self.golden_until = t + 4
                self.say("A GOLDEN fish! Lucky day!", 5)
            if self.mode == "land":
                self.next_move = t + 4
                self.target = self.x

    def _splash(self, x, y):
        for _ in range(10):
            self.jumps.append([x, y, random.uniform(-1, 1), random.uniform(-2.2, -1), 18])
        self.ripples.append([x, y + 4, 1])

    # ---------- update ----------
    def update(self, st, t):
        self.tick += 1
        kind, season, phase = st["kind"], st["season"], st["phase"]
        sleeping = st["sleeping"]
        temp_c = st["temp_c"]

        # waking up / going to bed
        if self.prev_sleeping is not None and sleeping != self.prev_sleeping:
            if sleeping:
                self.bedtime_until = t + 5
                self.activity = None
            else:
                self.wake_until = t + 6
                self.inside = False
                self.x = self.target = BED_X
                self.next_move = t + 7
                if st.get("rain_text"):
                    self.say(st["rain_text"], 7)
                if st.get("compliment"):
                    self.say(st["compliment"], 7)
        if self.prev_sleeping is None and sleeping:
            self.inside, self.x = True, BED_X        # started up at night: already in bed
        self.prev_sleeping = self.sleeping = sleeping

        # new message from the phone makes the otter happy
        if st["message"] and st["message"] != self.last_message and not sleeping:
            self.happy_until = t + 3
        self.last_message = st["message"]

        # a new treasure each day
        if not sleeping and t >= self.wake_until:
            found = self.state.find_treasure(st["now"].date(), season)
            if found:
                article = "some" if found == "sea glass" else ("an" if found[0] in "aeiou" else "a")
                self.say(f"Found {article} {found}!", 8)
                self.happy_until = t + 3

        # rainbow and puddles when the rain stops
        if self.prev_kind in RAINY and kind not in RAINY and kind != "snow":
            self.rainbow_start, self.rainbow_until = t, t + 45 * 60
        if kind in RAINY or kind == "snow":
            self.rainbow_until = 0
        if kind in RAINY:
            if t >= self.puddle_until:
                self.puddle_since = t
            self.puddle_until = t + 30 * 60
        self.prev_kind = kind

        # snow-otter builds up while it snows
        if kind == "snow":
            if self.snow_since is None:
                self.snow_since = t
        else:
            self.snow_since = None

        wind = st["wind"] or 0
        dry = kind not in RAINY and kind != "snow"
        day = phase == "day"
        warm = (temp_c is not None and temp_c >= SWIM_C and day
                and kind in ("clear", "partly", "cloudy") and not sleeping)
        self.kite_on = (dry and day and wind >= KITE_KMH and kind != "fog" and not sleeping
                        and self.mode == "land" and self.activity is None)
        campfire = (season == "summer" and st["now"].hour >= 19 and dry
                    and wind < 30 and not sleeping)

        # otter behaviour
        if sleeping:
            if self.mode != "land":
                self._splash(POND_EDGE_X + 30, 100)
                self.mode, self.x = "land", POND_EDGE_X
            if not self.inside:
                dx = BED_X - self.x
                self.x += max(-1.2, min(1.2, dx))
                self.moving = abs(dx) > 0.5
                if not self.moving or t >= self.bedtime_until:
                    self.inside, self.x, self.moving = True, BED_X, False
            if self.inside and self.tick % 22 == 0:
                self.zs.append([WINDOW[0] + 8, WINDOW[1] - 2, 0])
        elif self.mode == "swim":
            self.swim_x = 150 + math.sin(t * 0.12) * 8
            self.moving = False
            if t >= self.swim_until or not warm:
                self._splash(140, 100)
                self.mode, self.x, self.target = "land", POND_EDGE_X - 8, 80
                self.next_move = t + 3
        else:
            sleepy = st["mins_to_bed"] <= 20
            routine = self._routine(st)
            if self.dancing and self.mode == "land" and self.activity != "fetch":
                if self.activity != "dance":
                    self.activity, self.target = "dance", self.x
                routine = None
            elif self.activity == "dance":
                self.activity = None
            if self.activity == "dance":
                pass
            elif st.get("focus_left"):
                if self.activity not in ("focus", "fetch") and self.mode == "land":
                    self.activity, self.target = "focus", 58
                routine = None
            elif self.activity == "focus":
                self.activity = None
            if (routine and self.activity != routine and self.mode == "land"
                    and self.activity not in ("focus", "fetch", "dance")):
                self.activity, self.target = routine, 58
            elif not routine and self.activity in ("pancakes", "movie"):
                self.activity = None
            elif (not routine and campfire and self.activity not in ("campfire", "focus", "fetch", "dance")
                  and self.mode == "land"):
                self.activity, self.target = "campfire", CAMP_X - 38
            elif not campfire and self.activity == "campfire":
                self.activity = None
            if (self.mode == "land" and self.activity is None
                    and t >= self.next_move and t >= self.wake_until):
                self._choose_activity(st, t, warm, dry, wind)
            self._run_activity(st, t, kind, dry)

            dx = self.target - self.x
            self.moving = abs(dx) > 0.5
            if self.moving:
                spd = 1.4 if self.activity in ("bike", "fetch") else (0.45 if sleepy else 0.7)
                self.x += max(-spd, min(spd, dx))
            if self.mode == "to_pond":
                if not warm:
                    self.mode = "land"
                elif not self.moving:
                    self.mode, self.swim_until = "swim", t + random.uniform(25, 50)
                    self.swim_x = 150
                    self._splash(POND_EDGE_X + 30, 100)
            if t >= self.next_blink:
                self.blink_until = t + 0.2
                self.next_blink = t + random.uniform(2, 6)
            if sleepy and t >= self.next_yawn and t >= self.wake_until:
                self.yawn_until = t + 2
                self.next_yawn = t + random.uniform(15, 30)

        if t < self.happy_until and self.tick % 8 == 0:
            hx = self.swim_x - 20 if self.mode == "swim" else self.x + 4
            self.hearts.append([hx + random.uniform(0, 20), OTTER_Y - 2 + (30 if self.mode == "swim" else 0), 0])

        for z in self.zs:
            z[0] += 0.15
            z[1] -= 0.35
            z[2] += 1
        self.zs = [z for z in self.zs if z[2] < 50]
        for h in self.hearts:
            h[1] -= 0.5
            h[2] += 1
        self.hearts = [h for h in self.hearts if h[2] < 30]
        for j in self.jumps:
            j[0] += j[2]
            j[1] += j[3]
            j[3] += 0.18
            j[4] -= 1
        self.jumps = [j for j in self.jumps if j[4] > 0]
        self._update_extras(st, t)
        self._update_life(st, t)

        # clouds & fog
        for c in self.clouds:
            c[0] += c[2] * (3 if kind == "storm" else 1)
            if c[0] > W + 10:
                c[0] = -35
        self.fog_x = (self.fog_x + 0.15) % W

        self._update_rain(kind)
        self._update_snow(kind)

        # lightning
        if self.flash:
            self.flash -= 1
        elif kind == "storm" and random.random() < 0.006:
            self.flash = 6
            x, y, pts = random.uniform(40, 180), 24, []
            while y < GRASS_Y:
                pts.append((x, y))
                x += random.uniform(-6, 6)
                y += random.uniform(6, 12)
            pts.append((x, GRASS_Y))
            self.bolt = pts

        # falling leaves (autumn) or blossom (spring)
        if season != self.season:
            self.leaves, self.season = [], season
        target = {"autumn": 8, "spring": 6}.get(season, 0) if kind != "snow" else 0
        while len(self.leaves) < target:
            self.leaves.append(self._new_leaf(season, anywhere=True))
        del self.leaves[target:]
        lwind = 0.6 if kind == "storm" else 0.15
        for lf in self.leaves:
            lf[1] += lf[4]
            lf[0] += math.sin(self.tick * 0.08 + lf[2]) * 0.4 + lwind
            if lf[1] > lf[5] or lf[0] > W:
                lf[:] = self._new_leaf(season)

        # summer fireflies
        target = 14 if (season == "summer" and phase == "night"
                        and kind not in RAINY and kind != "snow") else 0
        while len(self.fireflies) < target:
            self.fireflies.append([random.uniform(0, W), random.uniform(60, 104), random.uniform(0, 6.28)])
        del self.fireflies[target:]
        for f in self.fireflies:
            f[0] = (f[0] + math.sin(t * 0.4 + f[2]) * 0.25) % W
            f[1] = max(58, min(106, f[1] + math.cos(t * 0.5 + f[2] * 1.3) * 0.15))

        # ducks paddle around the pond (keeping clear of a swimming otter)
        lo = 187 if self.mode == "swim" else 142
        self.duck_x += 0.12 * self.duck_dir
        if self.duck_x > 194:
            self.duck_dir = -1
        elif self.duck_x < lo:
            self.duck_dir = 1

        # New Year fireworks
        if "nye" in st["holidays"] and phase != "day":
            if len(self.rockets) < 3 and random.random() < 0.05:
                self.rockets.append([random.uniform(30, 180), GRASS_Y, random.uniform(-2.2, -1.6),
                                     random.choice(CONFETTI), random.uniform(16, 42)])
        for r in self.rockets:
            r[1] += r[2]
            if r[1] <= r[4]:
                for _ in range(18):
                    a, sp = random.uniform(0, 6.28), random.uniform(0.4, 1.1)
                    self.sparks.append([r[0], r[1], math.cos(a) * sp, math.sin(a) * sp, r[3], 28])
        self.rockets = [r for r in self.rockets if r[1] > r[4]]
        for s in self.sparks:
            s[0] += s[2]
            s[1] += s[3]
            s[3] += 0.03
            s[5] -= 1
        self.sparks = [s for s in self.sparks if s[5] > 0]

        # confetti on birthdays & New Year
        party = ((st["birthdays_today"] or "newyear" in st["holidays"] or self.otter_bday or t < self.burst_until)
                 and not sleeping)
        target = 40 if party else 0
        while len(self.confetti) < target:
            self.confetti.append([random.uniform(0, W), random.uniform(-H, 0),
                                  random.uniform(0.4, 0.9), random.choice(CONFETTI),
                                  random.uniform(0, 6.28)])
        del self.confetti[target:]
        for c in self.confetti:
            c[1] += c[2]
            c[0] += math.sin(self.tick * 0.1 + c[4]) * 0.4
            if c[1] > H:
                c[0], c[1] = random.uniform(0, W), -3

    def _choose_activity(self, st, t, warm, dry, wind):
        kind, temp_c = st["kind"], st["temp_c"]
        mild = temp_c is None or 5 <= temp_c <= 28
        opts = [("wander", 6.0)]
        if warm:
            opts.append(("swim", 3.0))
        if kind in RAINY:
            opts.append(("hobby", 5.0))
        if dry and t < self.puddle_until and kind != "snow":
            opts.append(("puddle", 6.0))
        if st["season"] == "autumn" and kind != "snow":
            opts.append(("leaves", 1.5))
        if dry and wind < CALM_KMH and st["phase"] == "day" and mild:
            opts.append(("bubbles", 1.5))
        if (kind in ("clear", "partly", "cloudy") and wind < BIKE_MAX_KMH and mild
                and st["phase"] == "day" and (st.get("bike_score") is None or st["bike_score"] >= 7)):
            opts.append(("bike", 1.5))
        if dry and st["phase"] == "day" and 0 <= self.state.garden_stage(st["now"].date()) <= 4:
            opts.append(("water", 1.2))
        opts.append(("trick", 2.0))
        total = sum(w for _, w in opts)
        r = random.uniform(0, total)
        for choice, w in opts:
            r -= w
            if r <= 0:
                break
        self.next_move = t + random.uniform(4, 10)
        if choice == "wander":
            self.target = random.uniform(26, 100)
        elif choice == "swim":
            self.mode, self.target = "to_pond", POND_EDGE_X
        else:
            self.activity, self.act_step = choice, 0
            if choice == "hobby":
                self.hobby_kind = random.choice(["book", "paint"])
                self.painting = []
                self.target = BED_X
                self.act_until = t + random.uniform(40, 80)
            elif choice == "puddle":
                self.target = random.choice(PUDDLES) - 16
                self.act_until = t + 60
            elif choice == "leaves":
                self.target = LEAF_PILE_X - 16
                self.act_until = t + 30
            elif choice == "bubbles":
                self.target = random.uniform(30, 90)
                self.act_until = t + 14
            elif choice == "bike":
                self.target = 100
                self.act_until = t + 40
            elif choice == "water":
                self.target = 0
                self.act_until = t + 25
            elif choice == "trick":
                known = self.state.tricks_known(st["now"].date())
                self.trick = random.choice(TRICKS[:known])
                self.target, self.trick_t, self.act_until = self.x, t, t + 3.2

    def _run_activity(self, st, t, kind, dry):
        a = self.activity
        if a is None:
            return
        arrived = abs(self.target - self.x) <= 0.5
        if a == "hobby":
            if kind not in RAINY or t >= self.act_until:
                self.activity = None
            elif arrived and self.hobby_kind == "paint" and self.tick % 25 == 0 and len(self.painting) < 40:
                self.painting.append((random.randrange(1, 7), random.randrange(1, 6),
                                      random.choice(CONFETTI + [(90, 170, 90), (250, 230, 120)])))
        elif a == "puddle":
            if not dry or t >= self.act_until:
                self.activity = None
            elif arrived and t - self.jump_t > 1.2:
                self.jump_t = t
                self.act_step += 1
                px = self.x + 16
                for _ in range(8):
                    self.jumps.append([px + random.uniform(-6, 6), 98, random.uniform(-1.2, 1.2),
                                       random.uniform(-2.4, -1.2), 16])
                if self.act_step >= 5:
                    self.activity, self.next_move = None, t + 3
                else:
                    others = [p - 16 for p in PUDDLES if abs(p - 16 - self.x) > 2]
                    self.target = random.choice(others)
        elif a == "leaves":
            if arrived and self.act_step == 0:
                self.act_step, self.jump_t, self.in_pile_until = 1, t, t + 3.2
                for _ in range(26):
                    self.jumps.append([LEAF_PILE_X + random.uniform(-9, 9), 92, random.uniform(-1.5, 1.5),
                                       random.uniform(-3, -1.2), 34,
                                       random.choice([(214, 110, 40), (230, 170, 60), (190, 60, 40)])])
            elif self.act_step == 1 and t >= self.in_pile_until:
                self.activity, self.happy_until, self.next_move = None, t + 2, t + 3
                self.target = self.x - 20
            elif t >= self.act_until:
                self.activity = None
        elif a == "bubbles":
            if arrived and self.tick % 7 == 0:
                self.bubbles.append([self.x + 30, OTTER_Y + 14, random.uniform(1.5, 3.5),
                                     random.uniform(0.2, 0.6), random.uniform(0, 6.28), 0])
            if t >= self.act_until or not dry:
                self.activity, self.next_move = None, t + 3
        elif a == "water":
            if arrived:
                if self.act_step == 0:
                    self.act_step, self.act_until = 1, t + 8
                if self.tick % 3 == 0:
                    self.jumps.append([self.x + 19 + random.uniform(-1, 1), OTTER_Y + 30, random.uniform(-0.5, -0.1),
                                       random.uniform(0.3, 0.7), 10, (150, 200, 245)])
            if t >= self.act_until or not dry:
                self.activity, self.next_move = None, t + 2
                self.target = 30
        elif a == "trick":
            if t >= self.act_until:
                self.activity, self.next_move = None, t + 3
        elif a == "fetch":
            b = self.ball
            if b is None or t >= self.act_until:
                self.activity, self.ball = None, None
                return
            if b["state"] == "landed":
                self.target = max(0, min(104, b["x"] - 16))
                if abs(self.target - self.x) <= 1:
                    b["state"] = "carried"
                    self.target = 50 if self.x > 60 else 80
            elif b["state"] == "carried" and arrived:
                b.update(state="dropped", x=self.x + 30, y=96.0, t=t)
                self.happy_until, self.activity, self.next_move = t + 3, None, t + 4
        elif a == "bike":
            if arrived:
                self.act_step += 1
                if self.act_step >= 3:
                    self.activity, self.next_move = None, t + 3
                else:
                    self.target = 26 if self.target > 60 else 100
            if t >= self.act_until:
                self.activity = None

    def _update_extras(self, st, t):
        for b in self.bubbles:
            b[0] += b[3] + math.sin(t * 2 + b[4]) * 0.2
            b[1] -= 0.35
            b[5] += 1
        self.bubbles = [b for b in self.bubbles if b[5] < 80 and b[1] > 0]
        cold = st["temp_c"] is not None and st["temp_c"] < 10
        if (cold or st["phase"] != "day") and self.tick % 12 == 0:      # chimney smoke
            self.smoke.append([CHIMNEY[0] + 2, CHIMNEY[1] - 1, 0, random.uniform(0, 6.28)])
        for sm in self.smoke:
            sm[0] += 0.12 + (st["wind"] or 0) / 200
            sm[1] -= 0.25
            sm[2] += 1
        self.smoke = [sm for sm in self.smoke if sm[2] < 60]
        if self.activity == "campfire" and self.tick % 3 == 0:
            self.embers.append([CAMP_X + random.uniform(-2, 2), 92, random.uniform(-0.2, 0.2), 0])
        for e in self.embers:
            e[0] += e[2]
            e[1] -= 0.45
            e[3] += 1
        self.embers = [e for e in self.embers if e[3] < 25]
        if self.activity == "dance" and self.tick % 10 == 0:
            self.notes.append([self.x + random.uniform(4, 28), OTTER_Y - 4, 0, random.choice(CONFETTI)])
        for n in self.notes:
            n[0] += math.sin(n[2] * 0.2) * 0.4
            n[1] -= 0.4
            n[2] += 1
        self.notes = [n for n in self.notes if n[2] < 40]

    def command(self, cmd, t, st):
        what, arg = cmd
        if what == "postcard":
            self.say(f"A postcard from {arg}!", 6)
            if not st["sleeping"]:
                self.happy_until = t + 3
            return
        if what != "throw":
            return
        if st["sleeping"]:
            for i in range(3):
                self.zs.append([WINDOW[0] + 8 + i * 3, WINDOW[1] - 2 - i * 4, 0])
            return
        if arg == "fish":
            self.thrown = {"t0": t}
        else:
            if self.mode != "land":
                self._splash(140, 100)
                self.mode, self.x = "land", POND_EDGE_X - 8
            self.activity, self.act_step, self.act_until = "fetch", 0, t + 40
            self.ball = {"x": -4.0, "y": 50.0, "vx": random.uniform(1.6, 2.4), "vy": -1.0, "state": "flying"}
            self.target = self.x

    def camera_event(self, ev, data, t, st):
        awake = not st["sleeping"]
        if ev == "presence":
            if data is not None:
                self.look_x, self.look_t = data, t
            if (awake and self.mode == "land" and self.activity is None
                    and t - self.last_greet > 45 and t >= self.wake_until):
                self.last_greet = t                 # noticed you: a little wave
                self.activity, self.trick, self.trick_t, self.act_until = "trick", "wave", t, t + 2
                self.target = self.x
        elif ev == "welcome" and awake:
            self.say("Welcome home!", 6)
            self.happy_until = t + 4
        elif ev == "wave":
            self.poke(t)
        elif ev == "cover" and awake:
            self.hiding = True
        elif ev == "uncover":
            if self.hiding and awake:
                self.say("Peekaboo!", 3)
                self.happy_until = t + 2
            self.hiding = False
        elif ev == "highfive" and awake and self.mode == "land":
            self.highfive_until = t + 1.6
            self.say("High five!", 3)
        elif ev == "dance_start":
            self.dancing = True
        elif ev == "dance_stop":
            self.dancing = False

    def focus_finished(self, t):
        self.say("Break time! Well done!", 8)
        self.happy_until = t + 4
        self.burst_until = t + 5
        if self.activity == "focus":
            self.activity = None

    def _routine(self, st):
        now = st["now"]
        if now.weekday() == 6 and 8 <= now.hour < 11:
            return "pancakes"
        if now.weekday() == 4 and now.hour >= 19 and st["mins_to_bed"] > 3:
            return "movie"
        return None

    def say(self, text, secs=6):
        self.speech_q.append((text, secs))

    def _update_life(self, st, t):
        now, kind, phase, season = st["now"], st["kind"], st["phase"], st["season"]
        today = now.date()
        day = phase == "day"
        dry = kind not in RAINY and kind != "snow"
        awake = not st["sleeping"]

        # speech bubbles queue
        if t >= self.find_until and self.speech_q:
            self.find_msg, dur = self.speech_q.pop(0)
            self.find_until = t + dur

        # the otter's own birthday
        od = None
        try:
            if st.get("otter_birthday_cfg"):
                m_, d_ = (int(v) for v in st["otter_birthday_cfg"].split("-"))
                od = dt.date(today.year, m_, d_)
        except Exception:
            od = None
        od = od or world_otter_day(today.year)
        self.otter_bday = today == od
        try:
            started = dt.date.fromisoformat(self.state.data["started"])
            self.otter_age = max(1, today.year - started.year)
        except Exception:
            self.otter_age = 1

        # new tricks, harvests
        if awake and t >= self.wake_until:
            known = self.state.tricks_known(today)
            if known > self.state.data.get("tricks_announced", 1):
                self.state.announce_trick(known)
                self.trick = TRICKS[known - 1]
                self.say(f"I learned a new trick: {self.trick}!", 6)
                if self.mode == "land" and self.activity is None:
                    self.activity, self.trick_t, self.act_until, self.target = "trick", t, t + 3.2, self.x
            if self.state.garden_stage(today) == 5 and day:
                self.state.replant(today)
                self.say("Harvest time! Yum!", 6)
                self.happy_until = t + 3
        self.garden = self.state.garden_stage(today)

        # birds hop about in the tree
        for b in self.birds:
            if random.random() < 0.01:
                b[2] = t

        # a heron drops by now and then
        if self.heron is None:
            if self.next_heron == 0.0:
                self.next_heron = t + random.uniform(600, 2400)
            elif t >= self.next_heron and day and kind not in ("storm", "snow"):
                self.heron = {"x": W + 12.0, "y": 24.0, "state": "in", "until": 0.0, "t": t}
        else:
            hr = self.heron
            if hr["state"] == "in":
                hr["x"] += (176 - hr["x"]) * 0.03 - 0.3
                hr["y"] += (64 - hr["y"]) * 0.05
                if abs(hr["x"] - 176) < 2 and abs(hr["y"] - 64) < 2:
                    hr.update(x=176.0, y=64.0, state="stand", until=t + random.uniform(60, 120))
            elif hr["state"] == "stand":
                has_fish = t < self.happy_until
                if has_fish and (self.mode == "swim" or self.x > 70):
                    hr.update(state="lunge", t=t)
                    self.say("Hey! That's MY fish!", 4)
                elif t >= hr["until"] or kind in ("storm",):
                    hr.update(state="out", t=t)
            elif hr["state"] == "lunge":
                if t - hr["t"] > 1.0:
                    hr.update(state="out", t=t)
            elif hr["state"] == "out":
                hr["x"] += 1.6
                hr["y"] -= 0.8
                if hr["x"] > W + 20:
                    self.heron, self.next_heron = None, t + random.uniform(1200, 3600)

        # frog and snail like it damp
        damp = kind in RAINY or t < self.puddle_until
        if 4 <= now.month <= 9 and damp and phase != "night":
            if self.frog is None:
                self.frog = {"x": 128.0, "from": 128.0, "to": 128.0, "t": -10.0}
            fr = self.frog
            if t - fr["t"] > 0.6 and random.random() < 0.012:
                fr.update({"from": fr["x"], "to": random.choice([116.0, 124.0, 134.0, 142.0]), "t": t})
            k = min(1.0, (t - fr["t"]) / 0.6)
            fr["x"] = fr["from"] + (fr["to"] - fr["from"]) * k
        else:
            self.frog = None
        self.snail_visible = 3 <= now.month <= 11 and damp and phase != "night"
        if self.snail_visible:
            self.snail_x -= 0.03
            if self.snail_x < 4:
                self.snail_x = 120.0

        # geese migrate: south in autumn, north in spring
        direction = -1 if now.month in (10, 11) else (1 if now.month == 3 else 0)
        if self.geese is None:
            if self.next_geese == 0.0:
                self.next_geese = t + random.uniform(20, 120)
            elif direction and t >= self.next_geese and day and kind not in ("storm", "fog"):
                self.geese = {"x": (W + 30.0) if direction < 0 else -50.0, "dir": direction}
        else:
            self.geese["x"] += 0.45 * self.geese["dir"]
            if self.geese["x"] < -60 or self.geese["x"] > W + 40:
                self.geese, self.next_geese = None, t + random.uniform(400, 900)

        # baby otters visit on spring days
        self.pups_on = (now.month in (4, 5) and 10 <= now.hour < 17 and dry and awake
                        and self.mode == "land" and self.activity not in ("bike",))
        if self.pups_on:
            for i in range(2):
                if self.x > 60:
                    goal = self.x - 18 - i * 14
                else:
                    goal = self.x + 34 + i * 14
                self.pups[i] += (goal - self.pups[i]) * 0.05

        # shooting stars on clear nights
        if phase == "night" and kind in ("clear", "partly") and random.random() < 0.0015:
            self.shooting.append([random.uniform(20, W - 20), random.uniform(4, 30),
                                  random.choice((-1, 1)) * 2.2, 1.0, 14])
        for sh in self.shooting:
            sh[0] += sh[2]
            sh[1] += sh[3]
            sh[4] -= 1
        self.shooting = [sh for sh in self.shooting if sh[4] > 0]

        # a fish thrown from the phone
        if self.thrown and t - self.thrown["t0"] >= 1.0:
            self.thrown = None
            self.happy_until = t + 4
        b = self.ball
        if b and b["state"] == "flying":
            b["x"] += b["vx"]
            b["y"] += b["vy"]
            b["vy"] += 0.08
            if b["y"] >= 96:
                b["y"] = 96.0
                b["vy"] *= -0.5
                b["vx"] *= 0.7
                if abs(b["vy"]) < 0.4:
                    b["state"] = "landed"
            if b["x"] > 100:
                b["vx"] = -abs(b["vx"]) * 0.5
        elif b and b["state"] == "dropped" and t - b["t"] > 12:
            self.ball = None
        if awake and now.hour == 15 and self.afternoon_said != today and st.get("compliment"):
            self.afternoon_said = today
            self.say(st["compliment"], 7)

        # golden fish leaps on lucky days
        self.lucky = day_hash(today, "golden") % 25 == 0
        if self.lucky and day and kind != "storm" and t >= self.next_leap:
            self.leap = {"t": t, "x": random.uniform(146, 186)}
            self.next_leap = t + random.uniform(20, 40)

    def _new_leaf(self, season, anywhere=False):
        if season == "autumn":
            col = random.choice([(214, 110, 40), (230, 170, 60), (190, 60, 40), (170, 100, 40)])
        else:
            col = random.choice([(250, 190, 214), (255, 230, 240)])
        x, y = random.uniform(3, 29), random.uniform(46, 62)
        if anywhere:
            x += random.uniform(0, 40)
            y += random.uniform(0, 25)
        return [x, y, random.uniform(0, 6.28), col, random.uniform(0.15, 0.3),
                random.uniform(GRASS_Y + 1, H - 10)]

    def _update_rain(self, kind):
        target = {"drizzle": 30, "rain": 80, "storm": 130}.get(kind, 0)
        while len(self.drops) < target:
            self.drops.append(self._new_drop(kind, anywhere=True))
        del self.drops[target:]
        wind = 1.2 if kind == "storm" else 0.0
        for d in self.drops:
            d[1] += d[2]
            d[0] += wind
            hit_umbrella = False
            if self.umbrella:
                cx, base, r = self.umbrella
                if abs(d[0] - cx) < r:
                    top = base - 0.75 * math.sqrt(r * r - (d[0] - cx) ** 2)
                    hit_umbrella = top <= d[1] <= base
            roof_y = None
            if 30 <= d[0] <= 80:
                roof_y = 61 - 21 * (1 - abs(d[0] - 55) / 25)
            if hit_umbrella:
                self.splashes.append([d[0], d[1] - 1, 3])
                d[:] = self._new_drop(kind)
            elif roof_y is not None and d[1] >= roof_y and d[1] < roof_y + 6:
                self.splashes.append([d[0], roof_y - 1, 3])
                d[:] = self._new_drop(kind)
            elif d[1] >= d[3]:
                if d[0] > 132 and 98 < d[3] < 114:
                    self.ripples.append([d[0], d[3], 1])
                else:
                    self.splashes.append([d[0], d[3], 3])
                d[:] = self._new_drop(kind)
        for s in self.splashes:
            s[2] -= 1
        self.splashes = [s for s in self.splashes if s[2] > 0]
        for r in self.ripples:
            r[2] += 0.5
        self.ripples = [r for r in self.ripples if r[2] < 6]

    def _update_snow(self, kind):
        target = 70 if kind == "snow" else 0
        while len(self.flakes) < target:
            self.flakes.append([random.uniform(0, W), random.uniform(-H, H),
                                random.uniform(0, 6.28), random.uniform(0.25, 0.6)])
        del self.flakes[target:]
        for f in self.flakes:
            f[1] += f[3]
            f[0] += math.sin(self.tick * 0.05 + f[2]) * 0.3
            if f[1] > H:
                f[0], f[1] = random.uniform(0, W), -2

    def _new_drop(self, kind, anywhere=False):
        speed = {"drizzle": 2.0, "rain": 3.5, "storm": 5.0}.get(kind, 3)
        x = random.uniform(-30 if kind == "storm" else 0, W)
        y = random.uniform(0, H) if anywhere else random.uniform(-10, 0)
        return [x, y, speed + random.uniform(-0.4, 0.4), random.uniform(GRASS_Y + 1, H - 1)]

    # ---------- draw ----------
    def draw(self, c, st, t):
        kind, phase, sleeping, season = st["kind"], st["phase"], st["sleeping"], st["season"]
        hol = st["holidays"]
        grey = kind in GREY
        night_like = phase == "night"
        c.blit(self._sky(("grey_" + ("night" if night_like else "day")) if grey else phase), (0, 0))

        aurora = (night_like and kind in ("clear", "partly") and st["now"].month in (9, 10, 11, 12, 1, 2, 3)
                  and ((st.get("kp") or 0) >= 6
                       or day_hash((st["now"] - dt.timedelta(hours=12)).date(), "aurora") % 40 == 0))
        if aurora:
            self._draw_aurora(c, t)
        if night_like and not grey:
            for x, y, tw in self.stars:
                bright = (self.tick // 4 + tw) % 25 != 0
                c.set_at((x, y), (255, 250, 220) if bright else (120, 120, 150))
            for sh in self.shooting:
                for k in range(6):
                    v = 255 - k * 38
                    c.set_at((int(sh[0] - sh[2] * k * 0.6), int(sh[1] - sh[3] * k * 0.6)), (v, v, max(0, v - 20)))

        if kind in ("clear", "partly"):
            if night_like:
                self._draw_moon(c, moon_phase(st["now"]))
            else:
                pd.circle(c, (250, 214, 90), (SUN_X, SUN_Y), 6)
                for i in range(8):
                    a = i * math.pi / 4 + (self.tick // 8 % 2) * math.pi / 8
                    x1, y1 = SUN_X + math.cos(a) * 8, SUN_Y + math.sin(a) * 8
                    x2, y2 = SUN_X + math.cos(a) * 11, SUN_Y + math.sin(a) * 11
                    pd.line(c, (250, 214, 90), (x1, y1), (x2, y2))

        if t < self.rainbow_until and not night_like:
            fade = min(1.0, (t - self.rainbow_start) / 20, (self.rainbow_until - t) / 600)
            self.rainbow.set_alpha(int(255 * max(0.0, fade)))
            c.blit(self.rainbow, (0, 0))

        n_clouds = {"clear": 1, "partly": 3, "fog": 4}.get(kind, 6)
        if kind == "storm":
            col = (50, 52, 66) if night_like else (96, 100, 116)
        elif kind in RAINY:
            col = (60, 62, 76) if night_like else (150, 156, 168)
        elif grey:
            col = (70, 74, 92) if night_like else (200, 204, 212)
        else:
            col = (90, 96, 124) if night_like else (250, 250, 255)
        for cx, cy, _, sc in self.clouds[:n_clouds]:
            self._cloud(c, cx, cy, sc, col)
        if self.geese:
            self._draw_geese(c)
        if self.heron and self.heron["state"] in ("in", "out"):
            self._draw_heron_flying(c)

        c.blit(self._land(season), (0, 0))
        if kind == "snow":
            c.fill((240, 244, 250), (0, GRASS_Y, W, 3))
            for x in range(0, W, 3):
                c.set_at((x, GRASS_Y + 3), (240, 244, 250))

        for i in range(4):                       # pond shimmer
            x = 136 + (i * 19 + self.tick // 3) % 60
            y = 100 + (i * 5) % 12
            pd.line(c, (150, 200, 240), (x, y), (x + 4, y))

        tulips = self._tulips(st["now"])
        if tulips:
            c.blit(tulips, (0, 0))
        if "halloween" in hol:
            c.blit(self.pumpkin, (-1, 74))
        self._draw_house(c, st, t)
        if season == "autumn":
            self._draw_leaf_pile(c)
        self._draw_puddles(c, t)
        if self.activity == "campfire" or season == "summer":
            self._draw_campfire(c, t, flames=False)
        self._draw_snow_otter(c, t)
        self._draw_garden(c, st)
        self._draw_sign_and_postcards(c, st)
        self._draw_birds(c, st, t)
        self._draw_holiday_props(c, st, t)
        if self.leap and t - self.leap["t"] < 1.2:
            k = (t - self.leap["t"]) / 1.2
            fx = int(self.leap["x"] + k * 14)
            fy = int(104 - math.sin(math.pi * k) * 12)
            pd.ellipse(c, (250, 200, 40), (fx - 3, fy - 1, 7, 3))
            c.set_at((fx - 4, fy), (250, 170, 30))
            if self.tick % 2:
                c.set_at((fx + 2, fy - 3), (255, 255, 200))

        if phase != "night" and kind != "storm":   # ducks
            bob = 1 if int(t * 1.5) % 2 else 0
            c.blit(self.duck[self.duck_dir], (int(self.duck_x) - 4, 97 + bob))
            if season == "spring" or st["now"].month == 6:
                for i, off in enumerate((10, 16)):
                    dxp = int(self.duck_x - self.duck_dir * off)
                    c.blit(self.duckling[self.duck_dir], (dxp - 2, 101 + ((bob + i) % 2)))

        back, front = self._flowers(season)
        front = [f for f in front if f[0] > 32]          # leave room for the garden
        self._draw_flowers(c, back, kind, t, kind == "snow")
        self._win_before = c.subsurface(self._window_area()).copy()
        if self.heron and self.heron["state"] in ("stand", "lunge"):
            self._draw_heron_standing(c, t)
        self._draw_small_friends(c, t)
        if self.pups_on:
            for i, px in enumerate(self.pups):
                bob = int(abs(math.sin(t * 8 + i)) * 2)
                c.blit(self.pup_sprite, (int(px), OTTER_Y + 13 - bob))
        self._draw_otter(c, st, t)
        if self.activity == "focus" and abs(self.target - self.x) <= 0.5 and not st["sleeping"]:
            self._draw_focus_desk(c, t)
        if self.otter_bday and not st["sleeping"]:
            self._draw_cake(c, t)
        if t < self.in_pile_until:                 # otter half-buried in the leaves
            self._draw_leaf_pile(c)
        self._draw_flowers(c, front, kind, t, kind == "snow")
        self._draw_bubbles(c)
        self._win_after = c.subsurface(self._window_area()).copy()

        if (4 <= st["now"].month <= 9 and phase == "day" and kind in ("clear", "partly")
                and (st["temp_c"] is None or st["temp_c"] >= BUTTERFLY_C)):
            for bx, ph, bcol in self.butterflies:
                x = int(bx + math.sin(t * 0.37 + ph) * 35 + math.sin(t * 1.3 + ph * 2) * 6)
                y = int(84 + math.sin(t * 0.8 + ph) * 10 + math.sin(t * 3.1 + ph) * 2)
                c.set_at((x, y), (40, 30, 30))
                if (self.tick + int(ph * 3)) % 4 < 2:
                    for dx_, dy_ in ((-1, 0), (1, 0), (-1, -1), (1, -1), (-2, -1), (2, -1)):
                        c.set_at((x + dx_, y + dy_), bcol)
                else:
                    c.set_at((x - 1, y - 1), bcol)
                    c.set_at((x + 1, y - 1), bcol)

        for lf in self.leaves:
            c.fill(lf[3], (int(lf[0]), int(lf[1]), 2, 1))
        for j in self.jumps:
            c.set_at((int(j[0]), int(j[1])), j[5] if len(j) > 5 else (190, 220, 250))

        tint = TINT[(phase, grey)]
        if tint:
            c.blit(self._overlay(tint, (W, H - 44)), (0, 44))

        # weather particles
        rain_col = (170, 200, 240)
        length = {"drizzle": 2, "rain": 3, "storm": 4}.get(kind, 3)
        wind = 1 if kind == "storm" else 0
        for d in self.drops:
            pd.line(c, rain_col, (d[0], d[1]), (d[0] + wind, d[1] + length))
        for s in self.splashes:
            c.set_at((int(s[0]) - 1, int(s[1]) - 1), rain_col)
            c.set_at((int(s[0]) + 1, int(s[1]) - 1), rain_col)
        for r in self.ripples:
            rr = int(r[2])
            pd.ellipse(c, (150, 190, 235), (r[0] - rr, r[1] - rr // 2, rr * 2 + 1, rr + 1), 1)
        for f in self.flakes:
            c.set_at((int(f[0]), int(f[1])), (250, 250, 255))
        if kind == "fog":
            for i, y in enumerate((56, 72, 92)):
                off = (self.fog_x * (1 + i * 0.5)) % W
                c.blit(self.fog, (off, y))
                c.blit(self.fog, (off - W, y))
        if self.flash:
            if self.flash > 2 and self.bolt:
                pd.lines(c, (255, 250, 200), False, self.bolt, 1)
            c.blit(self._overlay((255, 255, 255, self.flash * 18)), (0, 0))

        # things that glow in the dark
        self._draw_house_glow(c, st)
        if self.activity == "campfire":
            self._draw_campfire(c, t, flames=True)
        if "halloween" in hol and phase != "day":
            c.blit(self.pumpkin_glow, (-1, 74))
        if "halloween" in hol and phase == "night":
            for i, (ph, sp) in enumerate(self.bats):
                bx = int((t * 14 * sp + ph * 60) % (W + 20)) - 10
                by = int(28 + i * 9 + math.sin(t * 2 + ph) * 5)
                for ry, row in enumerate(BAT[(self.tick // 3 + i) % 2]):
                    for rx, b in enumerate(row):
                        if b == "1":
                            c.set_at((bx + rx, by + ry), (8, 6, 14))
        if "christmas" in hol:
            for i, (lx, ly) in enumerate(XMAS_LIGHTS):
                c.set_at((lx, ly), XMAS_COLOURS[(i + self.tick // 6) % 4])
            for dx_, dy_ in ((0, 0), (-1, 0), (1, 0), (0, -1), (0, 1)):
                c.set_at((15 + dx_, 43 + dy_), (255, 230, 90))
        for f in self.fireflies:
            b = (math.sin(t * 2.2 + f[2] * 3) + 1) / 2
            if b > 0.55:
                c.set_at((int(f[0]), int(f[1])), (230, 255, 120))
            if b > 0.85:
                for dx_, dy_ in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                    c.set_at((int(f[0]) + dx_, int(f[1]) + dy_), (120, 150, 60))
        for r in self.rockets:
            c.set_at((int(r[0]), int(r[1])), (255, 240, 200))
            c.set_at((int(r[0]), int(r[1]) + 2), (160, 120, 80))
        for s in self.sparks:
            col = s[4] if s[5] > 10 else tuple(v // 2 for v in s[4])
            c.set_at((int(s[0]), int(s[1])), col)

        # banners, bubbles and party things
        headlines = []
        if st["birthdays_today"]:
            names = " & ".join(b["name"] for b, _ in st["birthdays_today"])
            age = st["birthdays_today"][0][1] if len(st["birthdays_today"]) == 1 else None
            headlines.append(("banner", f"Happy birthday {names}!",
                              f"turns {age} today" if age else None, (255, 230, 120)))
        if "newyear" in hol:
            headlines.append(("banner", "Happy New Year!", str(st["now"].year), (255, 230, 120)))
        if self.otter_bday:
            headlines.append(("banner", "It's my birthday!", f"I'm {self.otter_age} today", (255, 230, 120)))
        if "kingsday" in hol:
            headlines.append(("banner", "Fijne Koningsdag!", None, (255, 150, 40)))
        if "pakjesavond" in hol:
            headlines.append(("banner", "Fijne pakjesavond!", None, (255, 120, 110)))
        if "christmas_day" in hol:
            headlines.append(("banner", "Merry Christmas!", None, (255, 120, 110)))
        if "halloween_day" in hol:
            headlines.append(("banner", "Happy Halloween!", None, (255, 170, 60)))
        if st["message"]:
            headlines.append(("bubble", st["message"]))

        if st["birthdays_today"] or "newyear" in hol or self.otter_bday or "kingsday" in hol:
            orange = "kingsday" in hol and not (st["birthdays_today"] or self.otter_bday)
            flags = [(255, 140, 30), (250, 110, 20), (255, 255, 255)] if orange else CONFETTI
            pd.line(c, (240, 230, 200), (46, 30), (154, 30))
            for i, x in enumerate(range(48, 150, 9)):
                pd.polygon(c, flags[i % len(flags)], [(x, 30), (x + 7, 30), (x + 3, 36)])
        for cf in self.confetti:
            c.fill(cf[3], (int(cf[0]), int(cf[1]), 2, 1))

        for z in self.zs:
            draw_text(c, "z" if z[2] < 20 else "Z", int(z[0]), int(z[1]), (220, 225, 255),
                      1 if z[2] < 25 else 2)
        for n in self.notes:                         # dance music notes
            x, y = int(n[0]), int(n[1])
            c.fill(n[3], (x, y + 2, 2, 2))
            c.fill(n[3], (x + 1, y - 2, 1, 4))
            c.set_at((x + 2, y - 2), n[3])
        for h in self.hearts:
            for ry, row in enumerate(HEART):
                for rx, b in enumerate(row):
                    if b == "1":
                        c.set_at((int(h[0]) + rx, int(h[1]) + ry), (255, 100, 130))

        if sleeping:
            c.blit(self._overlay((0, 0, 10, 80)), (0, 0))

        if sleeping and self.inside and not st["message"]:
            self._draw_dream(c, t)
        if self.ball:
            b = self.ball
            if b["state"] == "carried":
                bx, by = int(self.x) + 16, OTTER_Y + 20
            else:
                bx, by = int(b["x"]), int(b["y"])
            pd.circle(c, (210, 230, 70), (bx, by), 2)
            c.set_at((bx - 1, by - 1), (250, 255, 170))
        if self.thrown:
            k = min(1.0, t - self.thrown["t0"])
            sx, sy, ex, ey = W + 5, 30, int(self.x) + 16, OTTER_Y + 24
            if self.mode == "swim":
                ex, ey = int(self.swim_x), 100
            fx = sx + (ex - sx) * k
            fy = sy + (ey - sy) * k - math.sin(math.pi * k) * 25
            pd.ellipse(c, (120, 170, 200), (int(fx) - 4, int(fy) - 2, 8, 4))
            c.set_at((int(fx) + 4, int(fy)), (100, 150, 185))
        if t < self.wake_until:
            self._bubble(c, "Good morning!", *self._bubble_anchor(st), False)
        elif st.get("focus_left") and not sleeping:
            left = int(st["focus_left"])
            self._bubble(c, f"Focus {left // 60:02d}:{left % 60:02d}", *self._bubble_anchor(st), False)
        elif t < self.find_until and self.find_msg:
            self._bubble(c, self.find_msg, *self._bubble_anchor(st), False)
        elif headlines:
            item = headlines[int(t / 8) % len(headlines)]
            if item[0] == "banner":
                _, text, sub, col = item
                sc = 2 if text_width(text, 2) <= W - 8 else 1
                draw_text(c, text, (W - text_width(text, sc)) // 2, 40, col, sc, (60, 30, 40))
                if sub:
                    draw_text(c, sub, (W - text_width(sub)) // 2, 40 + 6 * sc, (255, 255, 255), 1, (60, 30, 40))
            else:
                self._bubble(c, item[1], *self._bubble_anchor(st), sleeping)

        self._draw_hud(c, st, t)

    # ---------- batch 1, part 2 drawing ----------
    def _draw_moon(self, c, phase):
        if isinstance(c, HiCanvas) and c.S > 1:       # smooth moon with craters at full detail
            S, surf = c.S, c.surf
            R = 6 * S
            cx, cy = SUN_X * S + S // 2, SUN_Y * S + S // 2
            k = math.cos(2 * math.pi * phase)
            craters = [(-0.3, -0.25, 0.22), (0.25, 0.2, 0.18), (0.1, -0.45, 0.12), (-0.35, 0.35, 0.1)]
            for dy in range(-R, R + 1):
                w = math.sqrt(max(0, R * R - dy * dy))
                for dx in range(-R, R + 1):
                    if dx * dx + dy * dy > R * R:
                        continue
                    lit = dx > k * w if phase < 0.5 else dx < -k * w
                    if lit:
                        col = (236, 236, 210)
                        for qx, qy, qr in craters:
                            if (dx / R - qx) ** 2 + (dy / R - qy) ** 2 < qr * qr:
                                col = (206, 206, 182)
                                break
                    else:
                        col = (50, 56, 84)
                    surf.set_at((cx + dx, cy + dy), col)
            return
        r, cx, cy = 6, SUN_X, SUN_Y
        k = math.cos(2 * math.pi * phase)
        for dy in range(-r, r + 1):
            w = math.sqrt(max(0, r * r - dy * dy))
            for dx in range(-r, r + 1):
                if dx * dx + dy * dy > r * r:
                    continue
                if phase < 0.5:
                    lit = dx > k * w
                else:
                    lit = dx < -k * w
                c.set_at((cx + dx, cy + dy), (236, 236, 210) if lit else (50, 56, 84))

    def _draw_aurora(self, c, t):
        if self.aurora_surf is None or self.tick % 4 == 0:
            a = pygame.Surface((W, 60), pygame.SRCALPHA)
            for x in range(W):
                top = 8 + math.sin(x * 0.045 + t * 0.25) * 7 + math.sin(x * 0.12 - t * 0.4) * 3
                length = 18 + math.sin(x * 0.08 + t * 0.3) * 8
                for k in range(int(length)):
                    fade = 1 - k / length
                    col = (90, 255, 160) if k > length * 0.3 else (190, 120, 255)
                    a.set_at((x, int(top + k)), (*col, int(120 * fade)))
            self.aurora_surf = a
        c.blit(self.aurora_surf, (0, 0))

    def _draw_geese(self, c):
        g = self.geese
        flap = (self.tick // 5) % 2
        for i, (ox_, oy_) in enumerate([(0, 0), (6, 3), (12, 6), (18, 9), (6, -3), (12, -6), (18, -9)]):
            x = int(g["x"] + ox_ * -g["dir"])
            y = 24 + oy_
            col = (40, 40, 48)
            if flap:
                c.set_at((x - 1, y - 1), col)
                c.set_at((x + 1, y - 1), col)
            else:
                c.set_at((x - 1, y + 1), col)
                c.set_at((x + 1, y + 1), col)
            c.set_at((x, y), col)

    def _draw_heron_standing(self, c, t):
        hr = self.heron
        spr = self.heron_sprite
        x, y = int(hr["x"]), int(hr["y"])
        if hr["state"] == "lunge":
            spr = hrotate(spr, 25)
            x -= 8
        elif int(t / 3) % 4 == 0:
            y += 2                                   # dips its head to fish
        c.blit(spr, (x, y))

    def _draw_heron_flying(self, c):
        hr = self.heron
        x, y = int(hr["x"]), int(hr["y"])
        up = (self.tick // 4) % 2
        grey = (150, 155, 165)
        pd.ellipse(c, grey, (x, y, 14, 5))
        pd.line(c, grey, (x, y + 2), (x - 6, y + 1))
        c.fill((230, 180, 60), (x - 9, y + 1, 3, 1))
        pd.line(c, (200, 170, 90), (x + 13, y + 3), (x + 20, y + 4))
        wy = y - 7 if up else y + 8
        pd.polygon(c, (120, 125, 140), [(x + 3, y + 2), (x + 11, y + 2), (x + 9, wy)])

    def _draw_small_friends(self, c, t):
        fr = self.frog
        if fr:
            k = min(1.0, (t - fr["t"]) / 0.6)
            hop = int(math.sin(math.pi * k) * 6) if k < 1 else 0
            x, y = int(fr["x"]), 101 - hop
            pd.ellipse(c, (80, 160, 70), (x - 3, y - 2, 7, 4))
            for ex in (x - 2, x + 2):
                c.set_at((ex, y - 3), (80, 160, 70))
                c.set_at((ex, y - 4), (20, 20, 20))
            c.fill((60, 130, 50), (x - 4, y + 1, 9, 1))
        if self.snail_visible:
            x, y = int(self.snail_x), 107
            c.fill((210, 190, 120), (x - 3, y + 2, 9, 2))
            c.set_at((x - 3, y), (210, 190, 120))
            c.set_at((x - 4, y - 1), (210, 190, 120))
            pd.circle(c, (150, 90, 50), (x + 2, y), 3)
            c.set_at((x + 2, y), (220, 170, 110))
            c.set_at((x + 3, y - 1), (110, 60, 30))

    def _draw_garden(self, c, st):
        x0, y0 = 3, 100
        soil, soil_dk = (120, 80, 50), (96, 62, 38)
        c.fill(soil, (x0, y0, 26, 10))
        for ry in range(3):
            pd.line(c, soil_dk, (x0 + 1, y0 + 2 + ry * 3), (x0 + 24, y0 + 2 + ry * 3))
        for px in range(x0 - 1, x0 + 28, 4):           # little fence
            c.fill((230, 220, 200), (px, y0 - 3, 1, 4))
        pd.line(c, (230, 220, 200), (x0 - 1, y0 - 2), (x0 + 27, y0 - 2))
        stage = self.garden
        if st["kind"] == "snow" or stage < 0:
            if st["kind"] == "snow":
                c.fill((240, 244, 250), (x0, y0, 26, 2))
            return
        green, dark = (90, 170, 70), (60, 130, 50)
        for i, col in enumerate(range(x0 + 2, x0 + 25, 4)):
            for ry in range(3):
                y = y0 + 1 + ry * 3
                if stage == 0:
                    c.set_at((col, y), (200, 180, 120))
                elif stage == 1:
                    c.set_at((col, y), green)
                elif stage == 2:
                    c.fill(green, (col - 1, y - 1, 3, 2))
                else:
                    if ry == 0:                         # carrots
                        c.fill(green, (col - 1, y - 2, 3, 2))
                        if stage >= 4:
                            c.fill((240, 130, 40), (col, y, 1, 2))
                    elif ry == 1:                       # lettuces
                        pd.circle(c, green if stage < 4 else (120, 200, 90), (col, y), 2)
                        c.set_at((col, y), dark)
                    else:                               # tomatoes
                        c.fill(dark, (col, y - 3, 1, 4))
                        if stage == 3:
                            c.set_at((col + 1, y - 2), (255, 230, 90))
                        else:
                            c.set_at((col + 1, y - 2), (230, 50, 40))
                            c.set_at((col - 1, y - 1), (230, 50, 40))

    def _draw_birds(self, c, st, t):
        if st["phase"] == "night" or st["kind"] in ("storm", "rain"):
            return
        for i, (bx, by, hop_t) in enumerate(self.birds):
            hop = 2 if 0 <= t - hop_t < 0.25 else 0
            y = by - hop
            c.fill((120, 80, 50), (bx, y, 3, 2))
            c.set_at((bx, y + 1), (220, 80, 50))         # robin's red chest
            c.set_at((bx + 3, y), (60, 40, 30))
            c.set_at((bx - 1, y), (240, 200, 80))

    def _draw_holiday_props(self, c, st, t):
        hol = st["holidays"]
        dx, dy, dw, dh = DOOR
        if "sinterklaas" in hol:                     # a wooden clog by the door, with a carrot for the horse
            x, y = dx + dw + 1, 90
            c.fill((235, 200, 90), (x, y, 7, 3))
            c.fill((200, 160, 60), (x, y + 2, 7, 1))
            c.fill((235, 200, 90), (x + 5, y - 1, 3, 1))
            c.fill((240, 130, 40), (x + 2, y - 3, 1, 3))
            c.set_at((x + 2, y - 4), (80, 160, 70))
        if "pakjesavond" in hol or "christmas_day" in hol:   # presents
            for i, (px, col, bow) in enumerate([(19, (220, 60, 70), (255, 220, 80)),
                                                (26, (70, 140, 220), (255, 255, 255)),
                                                (22, (90, 180, 90), (230, 60, 60))]):
                py = 90 if i < 2 else 85
                c.fill(col, (px, py, 6, 5))
                c.fill(bow, (px + 2, py, 2, 5))
                c.fill(bow, (px, py + 2, 6, 1))

    def _draw_cake(self, c, t):
        x, y = min(int(self.x) + 34, 104), 88
        c.fill((250, 240, 230), (x, y + 6, 10, 1))
        c.fill((250, 190, 210), (x + 1, y, 8, 6))
        c.fill((255, 255, 255), (x + 1, y, 8, 2))
        c.fill((120, 170, 230), (x + 4, y - 4, 2, 4))
        flick = (255, 220, 80) if self.tick % 4 < 2 else (255, 160, 60)
        c.set_at((x + 4, y - 5), flick)
        c.set_at((x + 5, y - 6), flick)

    def _draw_dream(self, c, t):
        wx, wy = WINDOW[0] + WINDOW[2], WINDOW[1] - 6
        for i, (ddx, ddy, r) in enumerate([(3, 0, 1), (7, -5, 2)]):
            pd.circle(c, (230, 232, 245), (wx + ddx, wy + ddy), r)
        bx, by = wx + 10, wy - 22
        pd.ellipse(c, (230, 232, 245), (bx, by, 22, 15))
        name = list(DREAMS)[int(t / 20) % len(DREAMS)]
        col, rows = DREAMS[name]
        ix = bx + 11 - len(rows[0]) // 2
        iy = by + 7 - len(rows) // 2
        for ry, row in enumerate(rows):
            for rx, b in enumerate(row):
                if b == "1":
                    c.set_at((ix + rx, iy + ry), col)

    # ---------- batch 1 scenery ----------
    def _draw_house(self, c, st, t):
        cfg = st.get("settings", {})
        wall = WALL_COLOURS.get(cfg.get("wall"), WALL_COLOURS["wood"])
        plank = tuple(max(0, v - 24) for v in wall)
        trim = (110, 70, 40)
        roof = ROOF_COLOURS.get(cfg.get("roof"), ROOF_COLOURS["red"])
        roof_dk = tuple(max(0, v - 40) for v in roof)
        c.fill(trim, (CHIMNEY[0] - 2, CHIMNEY[1], 6, 8))
        c.fill((140, 90, 60), (CHIMNEY[0] - 3, CHIMNEY[1] - 1, 8, 2))
        c.fill(wall, (HOUSE_X, 60, 42, 33))
        for y in range(63, 93, 4):
            pd.line(c, plank, (HOUSE_X, y), (HOUSE_X + 41, y))
        pd.polygon(c, roof, [(30, 61), (55, 40), (80, 61)])
        for k in range(1, 5):                     # roof tiles
            y = 40 + k * 4
            half = int(25 * (y - 40) / 21)
            pd.line(c, roof_dk, (55 - half, y), (55 + half, y))
        pd.lines(c, roof_dk, False, [(30, 61), (55, 40), (80, 61)])
        # door (opens briefly when the otter goes in or comes out)
        dx, dy, dw, dh = DOOR
        door_open = (self.sleeping and not self.inside) or (0 < self.wake_until - t < 6 and self.wake_until - t > 4)
        door_col = (60, 36, 24) if door_open else DOOR_COLOURS.get(cfg.get("door"), DOOR_COLOURS["brown"])
        c.fill(door_col, (dx, dy + 4, dw, dh - 4))
        pd.ellipse(c, door_col, (dx, dy, dw, 9))
        if not door_open:
            pd.line(c, tuple(max(0, v - 30) for v in door_col), (dx + dw // 2, dy + 2), (dx + dw // 2, dy + dh - 1))
            c.fill((240, 200, 90), (dx + dw - 4, dy + 15, 2, 2))
            self._draw_wreath(c, st, dx + dw // 2, dy + 8)
        # window: warm light in the evening and while the otter sleeps
        wx, wy, ww, wh = WINDOW
        lit = st["phase"] != "day" or self.inside
        glass = (255, 214, 120) if lit else (150, 196, 230)
        c.fill(trim, (wx - 1, wy - 1, ww + 2, wh + 2))
        c.fill(glass, (wx, wy, ww, wh))
        pd.line(c, trim, (wx + ww // 2, wy), (wx + ww // 2, wy + wh - 1))
        pd.line(c, trim, (wx, wy + wh // 2), (wx + ww - 1, wy + wh // 2))
        c.fill((90, 150, 80), (wx - 1, wy + wh + 1, ww + 2, 2))         # window box
        for i in range(0, ww + 2, 3):
            c.set_at((wx - 1 + i, wy + wh), CONFETTI[i % len(CONFETTI)])
        # treasure shelf
        c.fill(trim, (HOUSE_X + 2, 64, 38, 1))
        x = HOUSE_X + 3
        for name in self.state.treasures[-12:]:
            col, rows = TREASURES.get(name, TREASURES["pebble"])
            for ry, row in enumerate(rows):
                for rx, b in enumerate(row):
                    if b == "1":
                        c.set_at((x + rx, 64 - len(rows) + ry), col)
            x += len(rows[0]) + 0
            if x > HOUSE_X + 39:
                break

    def _draw_wreath(self, c, st, cx, cy):
        m = st["now"].month
        if m == 12:
            ring, dots, bow = (40, 120, 60), [(230, 50, 50), (255, 220, 80)], (220, 40, 50)
        elif m in (9, 10, 11):
            ring, dots, bow = (190, 110, 40), [(230, 170, 60), (170, 60, 40)], (120, 70, 40)
        elif m in (3, 4, 5):
            ring, dots, bow = (90, 160, 80), [(255, 170, 200), (255, 240, 120), (180, 150, 250)], (250, 170, 200)
        else:
            ring, dots, bow = (80, 150, 70), [(255, 210, 60), (255, 255, 255)], (255, 200, 40)
        pd.circle(c, ring, (cx, cy), 4, 2)
        for i in range(6):
            a = i * 1.047
            c.set_at((int(cx + math.cos(a) * 4), int(cy + math.sin(a) * 4)), dots[i % len(dots)])
        c.fill(bow, (cx - 1, cy + 4, 3, 2))

    def _draw_sign_and_postcards(self, c, st):
        cfg = st.get("settings", {})
        name = cfg.get("name", "")
        if name:
            w = text_width(name) + 4
            c.fill((120, 80, 45), (6, 92, 1, 8))
            c.fill((200, 160, 100), (2, 85, w, 8))
            c.fill((120, 80, 45), (2, 92, w, 1))
            draw_text(c, name, 4, 87, (70, 40, 20))
        cards = cfg.get("postcards", [])
        if cards:
            c.fill((120, 80, 45), (106, 62, 1, 34))
            pd.line(c, (230, 230, 230), (76, 64), (106, 63))
            for i, pc in enumerate(cards[-4:]):
                x = 79 + i * 7
                h = day_hash(dt.date(2000, 1, 1), pc["place"])
                col = [(250, 240, 210), (220, 235, 250), (250, 225, 225), (230, 250, 220)][h % 4]
                stamp = CONFETTI[h % len(CONFETTI)]
                c.fill(col, (x, 65, 6, 5))
                c.set_at((x + 4, 66), stamp)
                c.fill((150, 150, 160), (x + 1, 68, 3, 1))
                c.set_at((x + 2, 64), (140, 100, 60))

    def _draw_focus_desk(self, c, t):
        ox = int(self.x)
        y = OTTER_Y + 22
        c.fill((140, 95, 55), (ox, y, 32, 3))
        c.fill((110, 72, 40), (ox + 2, y + 3, 2, 8))
        c.fill((110, 72, 40), (ox + 28, y + 3, 2, 8))
        c.fill((170, 170, 180), (ox + 9, y - 1, 14, 1))
        c.fill((60, 64, 74), (ox + 10, y - 10, 12, 9))
        c.fill((120, 200, 240), (ox + 11, y - 9, 10, 7))
        for i in range(3):
            if (self.tick // 6 + i) % 3:
                c.fill((40, 80, 120), (ox + 12, y - 8 + i * 2, 4 + (i * 3) % 6, 1))

    def _window_area(self):
        wx, wy, ww, wh = WINDOW
        return pygame.Rect(wx - 4, wy - 4, ww + 8, wh + 8)

    def _draw_house_glow(self, c, st):
        """Re-light the window after the night tint, but only where nothing stands in front of it."""
        if (st["phase"] != "day" or self.inside) and self._win_before is not None:
            wx, wy, ww, wh = WINDOW
            area = self._window_area()
            before, after = self._win_before, self._win_after
            trim, pane, halo = (110, 70, 40), (255, 214, 120), (255, 200, 110)
            for y in range(area.h):
                for x in range(area.w):
                    if before.get_at((x, y)) != after.get_at((x, y)):
                        continue                         # the otter (or a flower) is in front here
                    px, py = area.x + x, area.y + y
                    if wx <= px < wx + ww and wy <= py < wy + wh:
                        col = trim if (px == wx + ww // 2 or py == wy + wh // 2) else pane
                    else:
                        r, g, b = c.get_at((px, py))[:3]
                        col = (r + (halo[0] - r) * 40 // 255, g + (halo[1] - g) * 40 // 255,
                               b + (halo[2] - b) * 40 // 255)
                    c.set_at((px, py), col)
        for sm in self.smoke:
            shade = 200 - sm[2]
            c.set_at((int(sm[0] + math.sin(sm[2] * 0.15 + sm[3]) * 1.5), int(sm[1])), (shade, shade, shade + 5))

    def _tulips(self, now):
        m, d = now.month, now.day
        if (m == 3 and d >= 20) or (m == 4 and d < 5):
            stage = 1
        elif (m == 4 and d >= 5) or (m == 5 and d < 5):
            stage = 2
        elif m == 5 and d < 20:
            stage = 3
        else:
            return None
        if stage not in self.tulip_cache:
            s = pygame.Surface((W, H), pygame.SRCALPHA)
            cols = [(230, 50, 60), (255, 210, 60), (245, 130, 190), (250, 140, 40), (160, 90, 210), (250, 250, 250)]
            for i, y in enumerate(range(64, 84, 3)):
                for x in range(128, 200):
                    s.set_at((x, y + 1), (60, 130, 66))
                    if stage == 1:
                        if x % 2:
                            s.set_at((x, y), (120, 180, 96))
                    elif stage == 2 or (x + i) % 3:
                        col = cols[i % len(cols)]
                        s.set_at((x, y), col if x % 2 else tuple(max(0, v - 30) for v in col))
            self.tulip_cache[stage] = s
        return self.tulip_cache[stage]

    def _draw_leaf_pile(self, c):
        x, y = LEAF_PILE_X, 90
        pd.ellipse(c, (170, 90, 36), (x - 11, y, 22, 9))
        pd.ellipse(c, (206, 120, 44), (x - 9, y + 1, 18, 6))
        rnd = random.Random(3)
        for _ in range(26):
            c.set_at((x + rnd.randint(-9, 9), y + rnd.randint(1, 7)),
                     rnd.choice([(230, 170, 60), (190, 60, 40), (150, 80, 30)]))

    def _draw_puddles(self, c, t):
        if t >= self.puddle_until:
            return
        grow = min(1.0, (t - self.puddle_since) / 60)
        shrink = min(1.0, (self.puddle_until - t) / 600)
        k = max(0.4, min(grow, shrink))
        for px in PUDDLES:
            w = int(22 * k)
            pd.ellipse(c, (60, 96, 140), (px - w // 2, 95, w, 6))
            pd.ellipse(c, (110, 160, 210), (px - w // 2 + 1, 96, w - 2, 4))
            c.fill((200, 225, 245), (px - w // 4, 97, max(1, w // 3), 1))

    def _draw_campfire(self, c, t, flames):
        x, y = CAMP_X, 96
        if not flames:
            c.fill((110, 70, 40), (x - 6, y, 12, 2))
            c.fill((90, 56, 30), (x - 4, y - 1, 8, 2))
            for i in range(6):
                c.set_at((x - 7 + i * 3, y + 2), (130, 130, 135))
            return
        c.blit(self._overlay((255, 160, 60, 45), (26, 18)), (x - 13, y - 14))
        for i in range(5):
            h = 4 + int((math.sin(t * 9 + i * 1.7) + 1) * 2.5)
            col = (255, 220, 90) if i in (1, 2, 3) else (250, 120, 40)
            c.fill(col, (x - 3 + i * 1.4, y - h, 2, h))
        c.fill((255, 245, 180), (x - 1, y - 3, 2, 3))
        for e in self.embers:
            c.set_at((int(e[0]), int(e[1])), (255, 180, 80) if e[3] < 15 else (180, 90, 40))

    def _draw_snow_otter(self, c, t):
        if self.snow_since is None:
            return
        stage = min(3, int((t - self.snow_since) / 20))
        if stage == 0:
            return
        x, base, white, shade = 112, 97, (246, 248, 252), (210, 220, 235)
        if stage >= 1:
            r = 4 if stage == 1 else 7
            pd.circle(c, white, (x, base - r), r)
            pd.circle(c, shade, (x + 2, base - r + 2), r - 2, 1)
        if stage >= 2:
            pd.circle(c, white, (x, base - 18), 5)
        if stage >= 3:
            for ex in (x - 4, x + 4):                       # otter ears
                pd.circle(c, white, (ex, base - 22), 2)
            c.set_at((x - 2, base - 19), (30, 30, 30))
            c.set_at((x + 2, base - 19), (30, 30, 30))
            c.fill((240, 130, 40), (x, base - 17, 2, 1))     # carrot nose
            pd.line(c, (110, 70, 40), (x - 7, base - 10), (x - 12, base - 14))
            pd.line(c, (110, 70, 40), (x + 7, base - 10), (x + 12, base - 14))
            c.fill((60, 120, 200), (x - 5, base - 14, 10, 2))   # little scarf

    def _draw_bubbles(self, c):
        for b in self.bubbles:
            r = int(b[2])
            pd.circle(c, (215, 235, 255), (int(b[0]), int(b[1])), r, 1)
            c.set_at((int(b[0]) - r // 2, int(b[1]) - r // 2), (255, 255, 255))

    def _bubble_anchor(self, st):
        if self.inside:
            return WINDOW[0] + WINDOW[2] // 2, WINDOW[1] - 2
        if self.mode == "swim":
            return int(self.swim_x) - 18, 94
        top = OTTER_Y - (10 if st["birthdays_today"] else 2)
        return int(self.x) + 16, top

    def _bubble(self, c, text, ax, ay, dim):
        lines = wrap_text(text, 24)[:3]
        if not lines:
            return
        bw = max(text_width(l) for l in lines) + 8
        bh = len(lines) * 7 + 4
        bx = max(2, min(W - bw - 2, ax - bw // 2))
        by = max(24, ay - bh - 5)
        paper = (170, 168, 175) if dim else (252, 248, 236)
        ink = (40, 34, 40)
        pd.polygon(c, paper, [(ax - 3, by + bh - 1), (ax + 3, by + bh - 1), (ax, by + bh + 4)])
        pd.line(c, ink, (ax - 3, by + bh), (ax, by + bh + 4))
        pd.line(c, ink, (ax + 3, by + bh), (ax, by + bh + 4))
        c.fill(ink, (bx + 1, by, bw - 2, bh))
        c.fill(ink, (bx, by + 1, bw, bh - 2))
        c.fill(paper, (bx + 1, by + 1, bw - 2, bh - 2))
        pd.line(c, paper, (ax - 2, by + bh - 1), (ax + 2, by + bh - 1))
        for i, line in enumerate(lines):
            draw_text(c, line, bx + (bw - text_width(line)) // 2, by + 3 + i * 7, ink)

    def _draw_flowers(self, c, flowers, kind, t, snowy):
        wind = 2.5 if kind == "storm" else 1.2 if kind in ("rain", "drizzle") else 0.6
        for x, base, fkind, petal, centre, stem, ph in flowers:
            sway = int(round(math.sin(t * 1.6 + ph) * wind))
            top = base - stem
            pd.line(c, (56, 120, 50), (x, base), (x + sway, top))
            c.set_at((x - 1, base - 2), (72, 146, 62))
            pal = {"a": petal, "b": centre or petal}
            for ry, row in enumerate(FLOWER_HEADS[fkind]):
                for rx, ch in enumerate(row):
                    if ch != ".":
                        c.set_at((x + sway - 1 + rx, top - 3 + ry), pal[ch])
            if snowy:
                c.set_at((x + sway, top - 4), (245, 248, 255))

    def _cloud(self, c, x, y, sc, col):
        for dx, dy, r in ((0, 4, 5), (7, 1, 6), (14, 3, 5), (19, 5, 4)):
            pd.circle(c, col, (int(x + dx * sc), int(y + dy * sc)), int(r * sc))
        c.fill(col, (int(x), int(y + 4 * sc), int(19 * sc), int(5 * sc)))

    def _draw_otter(self, c, st, t):
        sleeping, kind = st["sleeping"], st["kind"]
        temp_c = st["temp_c"]
        happy = t < self.happy_until
        self.umbrella = None
        hot = (temp_c is not None and temp_c >= SUNGLASSES_C and st["phase"] == "day"
               and kind not in RAINY)

        if self.mode == "swim":
            fx = int(self.swim_x) - 24
            fy = 97 + (1 if int(t * 1.2) % 2 else 0)
            c.blit(self.float_sprite, (fx, fy))
            if hot:
                c.fill((25, 25, 35), (fx + 3, fy + 6, 6, 3))
                c.set_at((fx + 4, fy + 6), (120, 140, 180))
            if st["birthdays_today"]:
                pd.polygon(c, (240, 90, 140), [(fx + 6, fy - 7), (fx + 2, fy + 2), (fx + 10, fy + 2)])
                pd.circle(c, (255, 220, 90), (fx + 6, fy - 7), 2)
            if happy:                               # eating a fish on its tummy
                pd.ellipse(c, (120, 170, 200), (fx + 20, fy + 3, 10, 5))
                pd.polygon(c, (100, 150, 185), [(fx + 29, fy + 5), (fx + 33, fy + 2), (fx + 33, fy + 8)])
            c.blit(self._overlay((*WATER, 210), (50, 6)), (fx - 1, fy + 12))
            for x in range(fx - 4, fx + 52, 4):
                c.set_at((x, fy + 12), (150, 200, 240))
            return

        if sleeping and self.inside:              # tucked up indoors
            return

        stretching = False
        act = self.activity
        arrived = abs(self.target - self.x) <= 0.5
        if sleeping:
            frame = "yawn"
        elif t < self.wake_until:
            el = 6 - (self.wake_until - t)
            if el < 2.5:
                frame, stretching = "sleep", True
            elif el < 4.5:
                frame = "yawn"
            else:
                frame = "happy"
        elif happy or (act in ("bike", "leaves", "puddle") and not arrived):
            frame = "happy"
        elif t < self.yawn_until:
            frame = "yawn"
        elif t < self.blink_until:
            frame = "blink"
        elif (st["birthdays_today"] or act == "campfire") and int(t) % 5 == 0:
            frame = "happy"
        else:
            frame = "open"

        if sleeping:
            bob = 0
        elif act == "bike":
            bob = 0
        elif happy:
            bob = abs(math.sin(t * 7)) * 4
        elif self.moving:
            bob = abs(math.sin(t * 9)) * 3
        else:
            bob = 0
        jt = t - self.jump_t
        if 0 <= jt < 0.7:
            bob += math.sin(math.pi * jt / 0.7) * 12
        if act == "dance":
            bob = abs(math.sin(t * 10)) * 4
            frame = "happy"
        ox = int(self.x) + (int(math.sin(t * 5) * 4) if act == "dance" else 0)
        oy = OTTER_Y - int(bob) - (6 if act == "bike" else 0)
        cx = ox + 16

        if act != "bike":
            pd.ellipse(c, (70, 130, 64), (ox + 2, OTTER_Y + 29, 28, 4))   # shadow

        if stretching:                            # big morning stretch
            k = int(abs(math.sin((6 - (self.wake_until - t)) * 2.5)) * 8)
            spr = hscale(self.sprites["sleep"], (32 - k // 2, 32 + k))
            c.blit(spr, (ox + k // 4, OTTER_Y - k))
            return

        if act == "bike":
            self._draw_bike(c, ox, t, behind=True)
        trick_drawn = False
        if act == "trick":
            k = min(1.0, max(0.0, (t - self.trick_t) / 3.0))
            spr = self.sprites["happy"]
            if self.trick == "spin":
                w = max(4, int(32 * abs(math.cos(k * math.pi * 4))))
                c.blit(hscale(spr, (w, 32)), (ox + 16 - w // 2, oy))
                trick_drawn = True
            elif self.trick == "handstand":
                lift = int(min(1.0, k * 4, (1 - k) * 4) * 4)
                c.blit(hrotate(spr, 180), (ox, oy - lift))
                trick_drawn = True
            elif self.trick == "backflip":
                jump = int(math.sin(math.pi * min(1.0, k * 1.6)) * 16)
                rot = hrotate(spr, -360 * min(1.0, k * 1.6))
                rw, rh = rot.get_size()
                c.blit(rot, (ox + 16 - rw // 2, oy + 16 - rh // 2 - jump))
                trick_drawn = True
        if not trick_drawn:
            c.blit(self.sprites[frame], (ox, oy))
            if frame == "open" and t - self.look_t < 4 and not self.hiding:   # eyes follow you
                shift = 2 if self.look_x > 0.33 else (-2 if self.look_x < -0.33 else 0)
                if shift:
                    face, white, black = PALETTE["C"], PALETTE["W"], PALETTE["E"]
                    for ex in (ox + 10, ox + 20):
                        c.fill(face, (ex, oy + 12, 2, 4))
                    for ex in (ox + 10 + shift, ox + 20 + shift):
                        c.fill(white, (ex, oy + 12, 2, 2))
                        c.fill(black, (ex, oy + 14, 2, 2))
            if self.hiding and not sleeping:            # peekaboo: paws over the eyes
                for px in (ox + 6, ox + 17):
                    c.fill((43, 29, 20), (px - 1, oy + 10, 11, 8))
                    c.fill((138, 90, 52), (px, oy + 11, 9, 6))
            if t < self.highfive_until and not sleeping:   # high five!
                c.fill((138, 90, 52), (ox + 27, oy + 2, 5, 12))
                c.fill((232, 207, 160), (ox + 28, oy + 2, 3, 3))
                c.fill((43, 29, 20), (ox + 27, oy + 1, 5, 1))
                if int(t * 8) % 2:
                    for ddx, ddy in ((-3, 0), (3, 0), (0, -3), (0, 3)):
                        c.set_at((ox + 30 + ddx, oy - 2 + ddy), (255, 240, 120))
        if act == "bike":
            self._draw_bike(c, ox, t, behind=False)
        dressed = not sleeping
        hol = st["holidays"]
        paws_busy = (happy or act in ("hobby", "bubbles", "campfire", "bike", "pancakes", "movie", "water",
                                      "trick", "focus", "fetch")
                     or self.kite_on or "oudjaar" in hol)

        if "christmas" in hol:                     # Christmas jumper
            red, white, green = (196, 40, 48), (245, 245, 245), (40, 130, 70)
            c.fill(red, (ox + 6, oy + 19, 20, 9))
            c.fill(red, (ox + 2, oy + 23, 6, 5))
            c.fill(red, (ox + 24, oy + 23, 6, 5))
            c.fill(green, (ox + 6, oy + 19, 20, 1))
            for i in range(4):
                c.set_at((ox + 9 + i * 4, oy + 23), white)
                c.set_at((ox + 10 + i * 4, oy + 22), white)
                c.set_at((ox + 11 + i * 4, oy + 23), white)
            c.fill(green, (ox + 6, oy + 27, 20, 1))

        under_roof = 30 <= cx <= 80
        if dressed and (kind in RAINY or t < self.puddle_until) and act != "bike":   # wellies
            for bx in (ox + 3, ox + 19):
                c.fill((245, 200, 40), (bx, oy + 27, 10, 5))
                c.fill((150, 110, 20), (bx, oy + 31, 10, 1))
                c.set_at((bx + 2, oy + 28), (255, 240, 150))

        cold = temp_c is not None and temp_c < SCARF_C
        if kind == "snow" or cold:                 # scarf, in your chosen colour
            sc = SCARF_COLOURS.get(st.get("settings", {}).get("scarf"), SCARF_COLOURS["red"])
            c.fill(sc, (ox + 5, oy + 19, 22, 3))
            c.fill(sc, (ox + 20, oy + 21, 3, 7))
            c.fill((240, 220, 220), (ox + 20, oy + 27, 3, 1))

        if act == "trick" and self.trick == "wave":   # waving paw
            wob = int(math.sin(t * 14) * 2)
            c.fill((43, 29, 20), (ox + 30, oy + 1 + wob, 6, 14))
            c.fill((138, 90, 52), (ox + 31, oy + 2 + wob, 4, 12))
            c.fill((232, 207, 160), (ox + 32, oy + 3 + wob, 2, 2))
        if act == "trick" and self.trick == "juggle":
            for i, col in enumerate(((230, 70, 70), (255, 210, 60), (80, 140, 230))):
                a = t * 6 + i * 2.09
                c.fill(col, (ox + 15 + int(math.cos(a) * 9), oy - 6 + int(math.sin(a) * 5), 3, 3))
        if trick_drawn:
            return

        if st["birthdays_today"] or self.otter_bday:   # party hat
            pd.polygon(c, (240, 90, 140), [(ox + 16, oy - 9), (ox + 10, oy + 6), (ox + 22, oy + 6)])
            pd.line(c, (255, 220, 90), (ox + 13, oy), (ox + 19, oy))
            pd.circle(c, (255, 220, 90), (ox + 16, oy - 9), 2)
        elif "kingsday" in hol:                    # orange crown for King's Day
            c.fill((255, 140, 30), (ox + 8, oy + 1, 16, 4))
            for kx in (ox + 8, ox + 13, ox + 18, ox + 23):
                c.fill((255, 140, 30), (kx, oy - 2, 2, 3))
            c.set_at((ox + 16, oy + 2), (230, 40, 60))
        elif "halloween" in hol:                   # witch's hat
            pd.polygon(c, (70, 40, 110), [(ox + 9, oy + 5), (ox + 23, oy + 5), (ox + 20, oy - 13)])
            pd.line(c, (70, 40, 110), (ox + 20, oy - 13), (ox + 25, oy - 10))
            c.fill((70, 40, 110), (ox + 3, oy + 4, 26, 3))
            c.fill((255, 150, 40), (ox + 10, oy + 2, 12, 2))
        elif kind == "snow" or (temp_c is not None and temp_c < BEANIE_C):   # beanie
            c.set_clip((ox, oy - 4, 32, 13))
            pd.ellipse(c, (60, 110, 190), (ox + 4, oy - 1, 24, 20))
            c.set_clip(None)
            c.fill((40, 80, 150), (ox + 3, oy + 6, 26, 3))
            pd.circle(c, (245, 245, 250), (ox + 16, oy - 2), 2)

        if dressed and hot and frame != "yawn":    # sunglasses
            for lx in (ox + 7, ox + 17):
                c.fill((25, 25, 35), (lx, oy + 11, 8, 5))
                c.set_at((lx + 1, oy + 12), (120, 140, 180))
            pd.line(c, (25, 25, 35), (ox + 15, oy + 12), (ox + 16, oy + 12))
            pd.line(c, (25, 25, 35), (ox + 3, oy + 12), (ox + 6, oy + 12))
            pd.line(c, (25, 25, 35), (ox + 25, oy + 12), (ox + 28, oy + 12))

        heatwave = temp_c is not None and temp_c >= HEATWAVE_C and kind not in RAINY
        if dressed and heatwave and not paws_busy:  # ice lolly and a little fan
            c.fill((120, 80, 40), (ox + 4, oy + 25, 1, 4))
            c.fill((250, 120, 160), (ox + 2, oy + 17, 5, 8))
            c.fill((255, 200, 220), (ox + 3, oy + 18, 1, 5))
            drip = int(t * 3) % 6
            c.set_at((ox + 3, oy + 25 + drip), (250, 140, 170))
            c.fill((80, 80, 90), (ox + 27, oy + 21, 2, 6))
            pd.circle(c, (180, 220, 240), (ox + 28, oy + 18), 4, 1)
            a = t * 20
            for k in range(3):
                ang = a + k * 2.09
                pd.line(c, (200, 230, 250), (ox + 28, oy + 18),
                                 (ox + 28 + math.cos(ang) * 3, oy + 18 + math.sin(ang) * 3))

        if happy and dressed:                      # a fish!
            gold = t < self.golden_until
            body, tail = ((250, 200, 40), (240, 170, 30)) if gold else ((120, 170, 200), (100, 150, 185))
            pd.ellipse(c, body, (ox + 9, oy + 23, 10, 5))
            pd.polygon(c, tail, [(ox + 18, oy + 25), (ox + 23, oy + 22), (ox + 23, oy + 28)])
            c.set_at((ox + 11, oy + 24), (20, 20, 30))
            if gold and self.tick % 3 == 0:
                c.set_at((ox + 8 + random.randrange(14), oy + 20 + random.randrange(8)), (255, 255, 200))
        elif dressed and act == "pancakes" and arrived:   # Sunday pancakes
            c.fill((235, 235, 240), (ox + 6, oy + 27, 20, 2))
            for i in range(4):
                c.fill((220, 160, 80) if i % 2 else (200, 140, 60), (ox + 9, oy + 25 - i * 2, 14, 2))
            c.fill((150, 80, 30), (ox + 11, oy + 18, 10, 1))
            c.fill((255, 240, 150), (ox + 14, oy + 17, 4, 1))
        elif dressed and act == "movie" and arrived:      # Friday movie night popcorn
            c.fill((230, 60, 60), (ox + 9, oy + 21, 14, 8))
            for sx in range(ox + 10, ox + 23, 3):
                c.fill((255, 255, 255), (sx, oy + 21, 2, 8))
            for i in range(6):
                c.fill((255, 245, 210), (ox + 9 + i * 2 + (self.tick // 5 + i) % 2, oy + 18 + (i % 2), 2, 2))
        elif dressed and "oudjaar" in hol and act is None:  # oliebollen on New Year's Eve
            c.fill((235, 235, 240), (ox + 6, oy + 27, 20, 2))
            for bx_, by_ in ((10, 23), (15, 23), (20, 23), (13, 19), (18, 19)):
                pd.circle(c, (170, 110, 50), (ox + bx_ + 1, oy + by_ + 1), 2)
                c.set_at((ox + bx_, oy + by_), (250, 250, 250))
        elif dressed and act == "water" and arrived:      # watering the garden
            c.fill((90, 150, 110), (ox + 24, oy + 20, 8, 6))
            pd.line(c, (90, 150, 110), (ox + 24, oy + 24), (ox + 19, oy + 29))
            pd.line(c, (60, 110, 80), (ox + 28, oy + 19), (ox + 30, oy + 17))

        if act == "hobby" and arrived:             # rainy-day hobby on the porch
            if self.hobby_kind == "book":
                c.fill((150, 60, 50), (ox + 7, oy + 21, 18, 8))
                c.fill((250, 246, 230), (ox + 8, oy + 22, 7, 6))
                c.fill((250, 246, 230), (ox + 17, oy + 22, 7, 6))
                for ly in (23, 25, 27):
                    pd.line(c, (170, 170, 180), (ox + 9, oy + ly), (ox + 13, oy + ly))
                    pd.line(c, (170, 170, 180), (ox + 18, oy + ly), (ox + 22, oy + ly))
            else:
                ex = ox + 30
                pd.line(c, (120, 80, 40), (ex + 1, oy + 31), (ex + 4, oy + 12))
                pd.line(c, (120, 80, 40), (ex + 8, oy + 31), (ex + 5, oy + 12))
                c.fill((250, 248, 240), (ex, oy + 14, 10, 8))
                for px, py, pc in self.painting:
                    c.set_at((ex + 1 + px, oy + 15 + py), pc)
                pd.line(c, (120, 80, 40), (ox + 26, oy + 24), (ex - 1, oy + 18 + int(math.sin(t * 6) * 2)))

        if act == "bubbles" and arrived:           # bubble wand
            pd.line(c, (200, 120, 200), (ox + 26, oy + 24), (ox + 29, oy + 16))
            pd.circle(c, (230, 160, 230), (ox + 30, oy + 14), 2, 1)

        if act == "campfire" and arrived:          # toasting a marshmallow
            tip = (CAMP_X - 2, 86)
            pd.line(c, (120, 80, 40), (ox + 27, oy + 24), tip)
            toast = min(1.0, ((t % 40) / 30))
            col = tuple(int(255 - (255 - v) * toast) for v in (200, 150, 90))
            c.fill(col, (tip[0] - 1, tip[1] - 2, 3, 3))

        if self.kite_on:                           # kite on a windy day
            kx = min(W - 12, ox + 64 + int(math.sin(t * 0.7) * 6))
            ky = 34 + int(math.sin(t * 1.3) * 5)
            pd.line(c, (230, 230, 230), (ox + 28, oy + 22), (kx, ky + 7))
            pts = [(kx, ky), (kx + 5, ky + 6), (kx, ky + 13), (kx - 5, ky + 6)]
            pd.polygon(c, (240, 80, 80), pts)
            pd.polygon(c, (255, 210, 70), [(kx, ky), (kx + 5, ky + 6), (kx, ky + 6)])
            pd.polygon(c, (255, 210, 70), [(kx, ky + 13), (kx - 5, ky + 6), (kx, ky + 6)])
            for i in range(4):
                tx = kx - 2 - i * 3
                ty = ky + 14 + i * 2 + int(math.sin(t * 6 + i) * 2)
                c.fill(CONFETTI[i % len(CONFETTI)], (tx, ty, 2, 1))

        if kind in RAINY and dressed and not under_roof and act != "bike":   # umbrella
            ucx, base, r = ox + 24, oy + 1, 14
            pts = [(ucx + r * math.cos(math.radians(a)), base - 0.75 * r * math.sin(math.radians(a)))
                   for a in range(180, -1, -15)]
            pd.line(c, (60, 40, 30), (ucx, base - 9), (ucx, oy + 25))
            pd.polygon(c, (214, 64, 64), pts)
            for a in (135, 90, 45):
                ex = ucx + r * math.cos(math.radians(a))
                ey = base - 0.75 * r * math.sin(math.radians(a))
                pd.line(c, (160, 40, 40), (ucx, base), (ex, ey))
            pd.line(c, (160, 40, 40), (ucx - r, base), (ucx + r, base))
            c.set_at((ucx, int(base - 0.75 * r) - 1), (60, 40, 30))
            self.umbrella = (ucx, base, r)

    def _draw_bike(self, c, ox, t, behind):
        frame_col, tyre = (40, 110, 80), (30, 30, 34)
        wy = OTTER_Y + 27
        w1, w2 = (ox + 4, wy), (ox + 28, wy)
        if behind:
            for wx, wy_ in (w1, w2):
                pd.circle(c, tyre, (wx, wy_), 5, 1)
                ang = self.x / 3
                for k in range(2):
                    a = ang + k * 1.57
                    pd.line(c, (150, 150, 160), (wx - math.cos(a) * 4, wy_ - math.sin(a) * 4),
                                     (wx + math.cos(a) * 4, wy_ + math.sin(a) * 4))
            pd.lines(c, frame_col, False, [w1, (ox + 14, wy), (ox + 12, wy - 9), w1])
            pd.lines(c, frame_col, False, [(ox + 14, wy), (ox + 25, wy - 9), w2])
            pd.line(c, frame_col, (ox + 12, wy - 9), (ox + 25, wy - 9))
        else:
            pd.line(c, (60, 60, 66), (ox + 25, wy - 9), (ox + 27, wy - 15))
            pd.line(c, (60, 60, 66), (ox + 24, wy - 15), (ox + 30, wy - 15))
            c.fill((220, 200, 120), (ox + 28, wy - 12, 3, 2))     # basket-ish lamp

    def _draw_hud(self, c, st, t):
        now = st["now"]
        dim = st["sleeping"]
        fg = (160, 165, 200) if dim else (255, 255, 255)
        sub = (130, 135, 170) if dim else (240, 240, 220)
        sh = (10, 10, 20)
        clock = now.strftime("%H:%M") if st["clock_24h"] else now.strftime("%I:%M").lstrip("0")
        draw_text(c, clock, 4, 4, fg, 2, sh)
        if not st["clock_24h"]:
            draw_text(c, now.strftime("%p"), 4 + text_width(clock, 2) + 3, 9, sub, 1, sh)
        draw_text(c, f"{now:%a} {now.day} {now:%b}", 4, 16, sub, 1, sh)

        if st["ok"] and st["temp"] is not None:
            temp = f"{round(st['temp'])}°"
            label = {"clear": "sunny" if st["phase"] == "day" else "clear",
                     "partly": "partly cloudy", "cloudy": "cloudy", "fog": "foggy",
                     "drizzle": "drizzle", "rain": "rain", "storm": "storm",
                     "snow": "snow"}[st["kind"]]
        else:
            temp, label = "--°", "offline"
        draw_text(c, temp, W - 4 - text_width(temp, 2), 4, fg, 2, sh)
        draw_text(c, label, W - 4 - text_width(label), 16, sub, 1, sh)
        if st.get("bike_score") is not None and st["ok"]:
            bike = f"bike {st['bike_score']}/10"
            draw_text(c, bike, W - 4 - text_width(bike), 23, sub, 1, sh)

        if st["reminders"]:
            msg = st["reminders"][int(t / 6) % len(st["reminders"])]
            c.fill((30, 24, 40), (0, H - 9, W, 9))
            c.fill((255, 210, 110) if not dim else (120, 100, 70), (0, H - 9, W, 1))
            col = (255, 220, 120) if not dim else (150, 135, 110)
            w = text_width(msg)
            if w <= W - 6:
                draw_text(c, msg, (W - w) // 2, H - 6, col)
            else:
                x = W - int(t * 20) % (w + W)
                draw_text(c, msg, x, H - 6, col)


# --------------------------------------------------------------------------
# Camera: turns movement in front of the frame into events for the otter.
# Only tiny 160x120 grey frames are looked at, in memory; nothing is saved or sent.
# --------------------------------------------------------------------------

ABSENCE_SECS = 2 * 3600          # "welcome home" after this long with nobody around


class GestureDetector:
    def __init__(self, sensitivity=1.0):
        self.sens = max(0.3, min(3.0, sensitivity))
        self.prev = self.bg = None
        self.base_bright = None
        self.hist = []                     # (time, motion fraction, centre x -1..1)
        self.last_motion = None
        self.covered, self.cover_t = False, None
        self.dancing = False
        self.still_big_since = None
        self.next_ok = {}

    def _ready(self, name, cooldown, t):
        if t >= self.next_ok.get(name, 0):
            self.next_ok[name] = t + cooldown
            return True
        return False

    @staticmethod
    def reversals(xs, amp):
        count, direction, ext = 0, 0, None
        for x in xs:
            if ext is None:
                ext = x
                continue
            d = x - ext
            if direction >= 0 and d < -amp:
                count += direction == 1
                direction, ext = -1, x
            elif direction <= 0 and d > amp:
                count += direction == -1
                direction, ext = 1, x
            elif (direction == 1 and x > ext) or (direction == -1 and x < ext):
                ext = x
        return count

    def process(self, gray, t):
        import numpy as np
        h, w = gray.shape[:2]
        f = gray[:h - h % 4, :w - w % 4].astype(np.float32)
        f = f.reshape(f.shape[0] // 4, 4, f.shape[1] // 4, 4).mean(axis=(1, 3))
        events = []
        bright = float(f.mean())
        if self.prev is None:
            self.prev, self.bg, self.base_bright, self.last_motion = f, f.copy(), bright, t
            return events

        # peekaboo: the camera suddenly goes dark (a hand over it) while the room is lit
        if not self.covered:
            if self.base_bright > 25 and bright < 0.35 * self.base_bright and float(f.std()) < 14:
                if self.cover_t is None:
                    self.cover_t = t
                elif t - self.cover_t > 0.4:
                    self.covered = True
                    events.append(("cover", None))
            else:
                self.cover_t = None
        if self.covered:
            if bright > 0.6 * self.base_bright:
                self.covered, self.cover_t, self.prev = False, None, f
                events.append(("uncover", None))
            return events

        diff = np.abs(f - self.prev)
        self.prev = f
        mask = diff > 12 / self.sens
        frac = float(mask.mean())
        cx = None
        if frac > 0.005:
            xs = np.nonzero(mask)[1]
            cx = float(xs.mean()) / max(1, f.shape[1] - 1) * 2 - 1
        self.base_bright += (bright - self.base_bright) * 0.01
        fg = float((np.abs(f - self.bg) > 25 / self.sens).mean())
        self.bg += (f - self.bg) * (0.08 if frac < 0.01 else 0.01)    # learn the room when it's calm

        self.hist.append((t, frac, cx))
        self.hist = [x for x in self.hist if t - x[0] <= 6]

        if frac > 0.02:
            if self.last_motion is not None and t - self.last_motion > ABSENCE_SECS:
                events.append(("welcome", None))
            self.last_motion = t
            if self._ready("presence", 0.5, t):
                events.append(("presence", cx))

        # wave: a hand moving side to side, quickly, for a moment
        recent = [x for (tt, fr, x) in self.hist if t - tt <= 1.5 and x is not None and 0.02 <= fr <= 0.12]
        if not self.dancing and self.reversals(recent, 0.08) >= 3 and self._ready("wave", 3, t):
            events.append(("wave", None))

        # dance: lots of back-and-forth movement for several seconds
        win = [x for x in self.hist if t - x[0] <= 5]
        if len(win) >= 15:
            active = sum(1 for x in win if x[1] > 0.04) / len(win)
            rev = self.reversals([x[2] for x in win if x[2] is not None and x[1] > 0.04], 0.1)
            if not self.dancing and active >= 0.8 and rev >= 6:
                self.dancing = True
                events.append(("dance_start", None))
            elif self.dancing and active < 0.3:
                self.dancing = False
                events.append(("dance_stop", None))

        # high five: something big (a hand) held still, close to the camera
        if fg > 0.4 and frac < 0.05 and bright > 0.5 * self.base_bright:
            if self.still_big_since is None:
                self.still_big_since = t
            elif t - self.still_big_since > 0.6 and self._ready("highfive", 6, t):
                events.append(("highfive", None))
                self.bg = f.copy()
        else:
            self.still_big_since = None
        return events


class CameraWatcher:
    def __init__(self, mirror=True, sensitivity=1.0):
        self.lock = threading.Lock()
        self.events = []
        self.mirror, self.sens = mirror, sensitivity
        try:
            import numpy  # noqa: F401
            from picamera2 import Picamera2  # noqa: F401
        except ImportError:
            print("[camera] picamera2 isn't installed, so camera features are off "
                  "(sudo apt install -y python3-picamera2)")
            return
        threading.Thread(target=self._run, daemon=True).start()

    def _run(self):
        from picamera2 import Picamera2
        try:
            cam = Picamera2()
            conf = cam.create_video_configuration(main={"size": (640, 480)},
                                                  lores={"size": (160, 120), "format": "YUV420"},
                                                  controls={"FrameRate": 10})
            cam.configure(conf)
            cam.start()
        except Exception as e:
            print(f"[camera] couldn't start the camera ({e}); camera features are off")
            return
        print("[camera] watching for waves, high fives and dancing")
        det = GestureDetector(self.sens)
        while True:
            try:
                yuv = cam.capture_array("lores")
                gray = yuv[:120, :160]
                if self.mirror:
                    gray = gray[:, ::-1]
                evs = det.process(gray, time.time())
                if evs:
                    with self.lock:
                        self.events.extend(evs)
            except Exception as e:
                print(f"[camera] frame error ({e})")
                time.sleep(1)

    def pop(self):
        with self.lock:
            evs, self.events = self.events, []
        return evs


# --------------------------------------------------------------------------
# Direct framebuffer output (used when SDL's kmsdrm/EGL route isn't available)
# --------------------------------------------------------------------------

class Framebuffer:
    """Draws straight into /dev/fb0, so no graphics libraries are needed."""

    def __init__(self, dev="/dev/fb0", sysfs=None):
        base = sysfs or "/sys/class/graphics/" + os.path.basename(dev)

        def rd(name):
            with open(os.path.join(base, name)) as f:
                return f.read().strip()

        self.bpp = int(rd("bits_per_pixel"))
        self.stride = int(rd("stride"))
        vw, vh = (int(v) for v in rd("virtual_size").split(","))
        self.w, self.h = vw, vh
        try:                                       # visible mode, e.g. "U:1920x1080p-0"
            mode = rd("modes").splitlines()[0].split(":")[1]
            self.w, self.h = (int(v) for v in mode.split("p")[0].split("i")[0].split("x"))
        except Exception:
            pass
        if self.bpp == 32:
            self.masks = (0xFF0000, 0x00FF00, 0x0000FF, 0)
        elif self.bpp == 16:
            self.masks = (0xF800, 0x07E0, 0x001F, 0)
        else:
            raise RuntimeError(f"unsupported framebuffer depth {self.bpp}")
        self.Bpp = self.bpp // 8
        self.file = open(dev, "r+b")
        self.mm = mmap.mmap(self.file.fileno(), self.stride * self.h)
        self.mm[:] = bytes(len(self.mm))           # clear to black
        self.tmp = None
        self._hide_console_cursor()

    @staticmethod
    def _hide_console_cursor():
        for path, data in (("/dev/tty1", "\033[?25l\033[2J"),
                           ("/sys/class/graphics/fbcon/cursor_blink", "0")):
            try:
                with open(path, "w") as f:
                    f.write(data)
            except Exception:
                pass

    def size(self):
        return self.w, self.h

    def show(self, img, pos):
        w, h = img.get_size()
        if self.tmp is None or self.tmp.get_size() != (w, h):
            self.tmp = pygame.Surface((w, h), 0, self.bpp, self.masks)
        self.tmp.blit(img, (0, 0))
        raw = self.tmp.get_buffer().raw
        pitch = self.tmp.get_pitch()
        n = w * self.Bpp
        x, y = pos
        for row in range(h):
            s = row * pitch
            d = (y + row) * self.stride + x * self.Bpp
            self.mm[d:d + n] = raw[s:s + n]


# --------------------------------------------------------------------------
# Main loop
# --------------------------------------------------------------------------

def rain_forecast(now, kind, hourly):
    """(text, probability in next 2 hours)."""
    soon = [p for tm, p, mm in hourly if now - dt.timedelta(minutes=30) <= tm <= now + dt.timedelta(hours=2)]
    prob_2h = max(soon) if soon else 0
    if kind in RAINY or kind == "snow":
        return None, prob_2h
    for tm, p, mm in hourly:
        if tm > now and (p >= 60 or mm >= 0.3):
            return f"Rain around {tm:%H:00} - take a coat!", prob_2h
    return None, prob_2h


def build_state(now, cfg, weather, book, board, sleep_start, wake, settings=None):
    w = weather.snapshot()
    sset = settings.snapshot() if settings else {}
    ups = book.upcoming(now.date(), cfg["birthday_lookahead_days"])
    hol = holidays_for(now)
    fahrenheit = cfg["temperature_unit"] == "fahrenheit"
    temp_c = None
    if w["temp"] is not None:
        temp_c = (w["temp"] - 32) * 5 / 9 if fahrenheit else w["temp"]
    sleeping = is_sleep_time(now, sleep_start, wake) and "nye" not in hol
    bed_m = sleep_start.hour * 60 + sleep_start.minute
    rain_text, prob_2h = rain_forecast(now, w["kind"], w.get("hourly") or [])
    word, meaning = daily_pick(WORDS, now.date(), "word")
    focus_left = None
    if sset.get("focus_until"):
        try:
            focus_left = (dt.datetime.fromisoformat(sset["focus_until"]) - dt.datetime.now()).total_seconds()
        except Exception:
            focus_left = None
    reminders = [reminder_text(n, b, age) for n, b, age in ups if n > 0]
    if rain_text:
        reminders.append(rain_text)
    return {
        "now": now,
        "sleeping": sleeping,
        "mins_to_bed": 9999 if "nye" in hol else (bed_m - (now.hour * 60 + now.minute)) % 1440,
        "phase": day_phase(now, w["sunrise"], w["sunset"]),
        "season": season_of(now),
        "holidays": hol,
        "kind": w["kind"], "temp": w["temp"], "temp_c": temp_c, "ok": w["ok"],
        "wind": w.get("wind"),
        "kp": w.get("kp"),
        "otter_birthday_cfg": cfg.get("otter_birthday", ""),
        "fahrenheit": fahrenheit,
        "clock_24h": cfg["clock_24h"],
        "birthdays_today": [(b, age) for n, b, age in ups if n == 0],
        "reminders": reminders,
        "message": board.current(),
        "settings": sset,
        "rain_text": rain_text,
        "bike_score": cycling_score(w["kind"], w.get("wind"), temp_c, prob_2h) if w["ok"] else None,
        "compliment": daily_pick(COMPLIMENTS, now.date(), "kind"),
        "focus_left": focus_left if focus_left and focus_left > 0 else None,
        "focus_expired": focus_left is not None and focus_left <= 0,
    }


def main():
    ap = argparse.ArgumentParser(description="Otter Pal - a retro otter for your wall")
    ap.add_argument("--windowed", action="store_true", help="run in a window (for testing)")
    ap.add_argument("--weather", choices=WEATHER_KINDS, help="force a weather type")
    ap.add_argument("--temp", type=float, help="force a temperature (in your configured unit)")
    ap.add_argument("--wind", type=float, help="force a wind speed in km/h")
    ap.add_argument("--demo", action="store_true", help="cycle through every weather type")
    ap.add_argument("--time", help="pretend it's this time, e.g. 23:15")
    ap.add_argument("--date", help="pretend it's this date, e.g. 2026-12-25")
    ap.add_argument("--snapshot", help="render a frame to this PNG and exit")
    ap.add_argument("--frames", type=int, default=60, help="frames to simulate before --snapshot")
    args = ap.parse_args()

    cfg = load_config()
    sleep_start, wake = parse_hm(cfg["sleep_time"]), parse_hm(cfg["wake_time"])
    book = BirthdayBook(BIRTHDAYS_PATH)
    board = MessageBoard(MESSAGE_PATH)
    settings = Settings(SETTINGS_PATH)
    weather = Weather(cfg, forced=args.weather)
    if cfg.get("web_port") and not args.snapshot:
        start_web_server(book, board, settings, int(cfg["web_port"]))

    offset = dt.timedelta(0)
    if args.time or args.date:
        real = dt.datetime.now()
        d = dt.date.fromisoformat(args.date) if args.date else real.date()
        tm = parse_hm(args.time) if args.time else real.time()
        offset = dt.datetime.combine(d, tm) - real

    if args.snapshot:
        os.environ["SDL_VIDEODRIVER"] = "dummy"
    fb = None
    use_fb = cfg.get("display", "auto") == "framebuffer" and not (args.windowed or args.snapshot)
    if use_fb:
        os.environ["SDL_VIDEODRIVER"] = "dummy"
    pygame.display.init()   # no audio needed
    if args.windowed or args.snapshot:
        screen = pygame.display.set_mode((W * 4, H * 4))
    elif not use_fb:
        try:
            screen = pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
            pygame.mouse.set_visible(False)
        except pygame.error as e:
            print(f"[display] normal screen output failed ({e}); drawing straight to /dev/fb0 instead")
            use_fb = True
            pygame.display.quit()
            os.environ["SDL_VIDEODRIVER"] = "dummy"
            pygame.display.init()
    if use_fb:
        pygame.display.set_mode((1, 1))
        fb = Framebuffer()
        print(f"[display] framebuffer {fb.w}x{fb.h}, {fb.bpp}-bit")
        sw, sh = fb.size()
    else:
        pygame.display.set_caption("Otter Pal")
        sw, sh = screen.get_size()
    scale = max(1, min(sw // W, sh // H))
    out_size = (W * scale, H * scale)
    out_pos = ((sw - out_size[0]) // 2, (sh - out_size[1]) // 2)
    # draw at the finest detail that divides evenly into the screen, capped to keep the Pi quick
    global HI_S
    divisors = [d for d in range(2, 6) if scale % d == 0]
    HI_S = max(divisors) if divisors else (scale if scale <= 7 else 1)
    wanted = cfg.get("detail", "auto")
    if wanted != "auto":                     # lower this in config.json if the Pi ever feels slow
        options = [d for d in range(1, scale + 1) if scale % d == 0 and d <= int(wanted)]
        HI_S = max(options) if options else 1
    final_zoom = scale // HI_S
    print(f"[display] {sw}x{sh}: world x{scale}, drawn at x{HI_S}, zoom x{final_zoom}")

    camera = None
    if cfg.get("camera", True) and not args.snapshot and not args.windowed:
        camera = CameraWatcher(cfg.get("camera_mirror", True), float(cfg.get("camera_sensitivity", 1.0)))
    keys_to_events = {pygame.K_w: ("wave", None), pygame.K_h: ("highfive", None),
                      pygame.K_m: ("welcome", None), pygame.K_LEFT: ("presence", -0.8),
                      pygame.K_RIGHT: ("presence", 0.8)}
    pending_events = []
    canvas = new_canvas(W, H)
    testing = bool(args.snapshot or args.demo or args.weather or args.time or args.date
                   or args.temp is not None or args.wind is not None)
    world = World(OtterState(STATE_PATH, persist=not testing))
    clock = pygame.time.Clock()
    last_reload = 0.0
    frame = 0
    running = True

    while running:
        t = time.time()
        for e in pygame.event.get():
            if e.type == pygame.QUIT:
                running = False
            elif e.type == pygame.KEYDOWN and e.key in (pygame.K_ESCAPE, pygame.K_q):
                running = False
            elif e.type == pygame.KEYDOWN and e.key in keys_to_events:
                pending_events.append(keys_to_events[e.key])        # pretend camera, for testing
            elif e.type == pygame.KEYDOWN and e.key == pygame.K_p:
                pending_events.append(("uncover" if world.hiding else "cover", None))
            elif e.type == pygame.KEYDOWN and e.key == pygame.K_d:
                pending_events.append(("dance_stop" if world.dancing else "dance_start", None))
            elif e.type == pygame.MOUSEBUTTONDOWN:
                world.poke(t)

        if t - last_reload > 30:
            book.maybe_reload()
            last_reload = t

        if args.demo:
            weather.forced = DEMO_ORDER[int(t / 8) % len(DEMO_ORDER)]
        st = build_state(dt.datetime.now() + offset, cfg, weather, book, board, sleep_start, wake, settings)
        if args.wind is not None:
            st["wind"] = args.wind
        if args.temp is not None:
            st["temp"] = args.temp
            st["temp_c"] = (args.temp - 32) * 5 / 9 if st["fahrenheit"] else args.temp

        if st["focus_expired"]:
            settings.stop_focus()
            world.focus_finished(t)
        for cmd in settings.pop_commands():
            world.command(cmd, t, st)
        if camera:
            pending_events.extend(camera.pop())
        for ev, data in pending_events:
            world.camera_event(ev, data, t, st)
        pending_events = []
        LIVE.update(bike_score=st["bike_score"], rain_text=st["rain_text"])
        world.update(st, t)
        world.draw(canvas, st, t)
        scaled = canvas.surf if final_zoom == 1 else pygame.transform.scale(canvas.surf, out_size)
        if fb:
            fb.show(scaled, out_pos)
        else:
            screen.fill((0, 0, 0))
            screen.blit(scaled, out_pos)
            pygame.display.flip()

        frame += 1
        if args.snapshot and frame >= args.frames:
            pygame.image.save(screen, args.snapshot)
            running = False
        if not args.snapshot:
            clock.tick(8 if st["sleeping"] else (12 if fb else FPS))

    pygame.quit()


if __name__ == "__main__":
    main()
