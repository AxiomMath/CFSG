module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainAbelData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1CohData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open CFSG.EvenSmallLie.UnitarySix.YamadaPar Stage1

@[expose] def m4Get (A : Array (Array ℕ)) (i j : ℕ) : ℕ := (A.getD i #[]).getD j 0

@[expose] def mul4 (A B : Array (Array ℕ)) : Array (Array ℕ) :=
  Array.ofFn (n := 6) fun i => Array.ofFn (n := 6) fun j =>
    (∑ k : Fin 6, m4Get A i k * m4Get B k j) % 4

@[expose] def add4 (A B : Array (Array ℕ)) : Array (Array ℕ) :=
  Array.ofFn (n := 6) fun i => Array.ofFn (n := 6) fun j => (m4Get A i j + m4Get B i j) % 4

@[expose] def sub4 (A B : Array (Array ℕ)) : Array (Array ℕ) :=
  Array.ofFn (n := 6) fun i => Array.ofFn (n := 6) fun j =>
    (m4Get A i j + 3 * m4Get B i j) % 4

@[expose] def one4 : Array (Array ℕ) :=
  Array.ofFn (n := 6) fun i => Array.ofFn (n := 6) fun j => if (i : ℕ) = j then 1 else 0

@[expose] def lift2 (M : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 6) fun i => Array.ofFn (n := 6) fun j => if (M.getD i 0).testBit j then 1 else 0

@[expose] def mv4 (A : Array (Array ℕ)) (v : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 6) fun i => (∑ k : Fin 6, m4Get A i k * v.getD k 0) % 4

@[expose] def dig4 (n : ℕ) : Array ℕ := Array.ofFn (n := 6) fun j => n / 4 ^ (j : ℕ) % 4

@[expose] def c0Rows : Eps → ℕ → Array ℕ
  | .plus, 0 => #[0, 0, 0, 16, 4, 0]
  | .plus, 1 => #[0, 0, 4, 8, 0, 0]
  | .plus, 2 => #[0, 0, 4, 8, 0, 0]
  | .plus, 3 => #[25, 24, 0, 35, 35, 56]
  | .plus, 4 => #[9, 53, 0, 8, 61, 40]
  | .plus, 5 => #[15, 0, 55, 0, 55, 46]
  | .minus, 0 => #[0, 0, 0, 8, 0, 32]
  | .minus, 1 => #[0, 0, 8, 0, 0, 41]
  | .minus, 2 => #[8, 4, 8, 4, 21, 44]
  | .minus, 3 => #[8, 37, 61, 0, 0, 40]
  | .minus, 4 => #[8, 0, 37, 0, 37, 40]
  | _, _ => zero6

@[expose] def kWord : List ℕ := [1, 2, 3, 0, 2, 0, 1]

@[expose] def kRows : Array ℕ := #[57, 30, 52, 24, 16, 32]

@[expose] def sqWit : List (ℕ × ℕ × Bool) :=
  [(0, 0, true), (576, 4016, false), (128, 2592, true), (704, 1424, false),
    (2064, 1104, false), (2640, 960, false), (2192, 3696, false), (2768, 2528, false),
    (32, 2208, true), (608, 1808, false), (160, 640, true), (736, 3376, false),
    (2096, 3312, false), (2672, 2912, false), (2224, 1744, false), (2800, 320, false),
    (2052, 2704, true), (2628, 3456, false), (2180, 176, true), (2756, 1952, false),
    (20, 1632, false), (596, 464, false), (148, 3136, false), (724, 3056, false),
    (2084, 560, true), (2660, 1312, false), (2212, 2064, true), (2788, 3840, false),
    (52, 3776, false), (628, 2416, false), (180, 1248, false), (756, 848, false),
    (8, 32, true), (584, 3984, false), (136, 2560, true), (712, 1456, false),
    (2072, 1136, false), (2648, 992, false), (2200, 3664, false), (2776, 2496, false),
    (40, 2176, true), (616, 1840, false), (168, 672, true), (744, 3344, false),
    (2104, 3280, false), (2680, 2880, false), (2232, 1776, false), (2808, 352, false),
    (2060, 2736, true), (2636, 3488, false), (2188, 144, true), (2764, 1920, false),
    (28, 1600, false), (604, 496, false), (156, 3168, false), (732, 3024, false),
    (2092, 528, true), (2668, 1280, false), (2220, 2096, true), (2796, 3872, false),
    (60, 3808, false), (636, 2384, false), (188, 1216, false), (764, 880, false),
    (1, 2288, true), (577, 1344, false), (129, 720, true), (705, 3936, false),
    (2065, 3616, false), (2641, 2448, false), (2193, 1024, false), (2769, 944, false),
    (33, 80, true), (609, 3552, false), (161, 2672, true), (737, 1984, false),
    (2097, 1664, false), (2673, 304, false), (2225, 3232, false), (2801, 2832, false),
    (2053, 576, true), (2629, 1872, false), (2181, 2144, true), (2757, 3440, false),
    (21, 3120, false), (597, 2976, false), (149, 1552, false), (725, 384, false),
    (2085, 2784, true), (2661, 4080, false), (2213, 192, true), (2789, 1488, false),
    (53, 1168, false), (629, 768, false), (181, 3760, false), (757, 2336, false),
    (9, 2256, true), (585, 1376, false), (137, 752, true), (713, 3904, false),
    (2073, 3584, false), (2649, 2480, false), (2201, 1056, false), (2777, 912, false),
    (41, 112, true), (617, 3520, false), (169, 2640, true), (745, 2016, false),
    (2105, 1696, false), (2681, 272, false), (2233, 3200, false), (2809, 2864, false),
    (2061, 608, true), (2637, 1904, false), (2189, 2112, true), (2765, 3408, false),
    (29, 3088, false), (605, 2944, false), (157, 1584, false), (733, 416, false),
    (2093, 2752, true), (2669, 4048, false), (2221, 224, true), (2797, 1520, false),
    (61, 1200, false), (637, 800, false), (189, 3728, false), (765, 2304, false),
    (2, 160, true), (578, 3856, false), (130, 2688, true), (706, 1328, false),
    (2066, 1264, false), (2642, 864, false), (2194, 3792, false), (2770, 2368, false),
    (34, 2048, true), (610, 1968, false), (162, 544, true), (738, 3472, false),
    (2098, 3152, false), (2674, 3008, false), (2226, 1648, false), (2802, 480, false),
    (2054, 2608, true), (2630, 3360, false), (2182, 16, true), (2758, 1792, false),
    (22, 1728, false), (598, 368, false), (150, 3296, false), (726, 2896, false),
    (2086, 656, true), (2662, 1408, false), (2214, 2224, true), (2790, 4000, false),
    (54, 3680, false), (630, 2512, false), (182, 1088, false), (758, 1008, false),
    (10, 128, true), (586, 3888, false), (138, 2720, true), (714, 1296, false),
    (2074, 1232, false), (2650, 832, false), (2202, 3824, false), (2778, 2400, false),
    (42, 2080, true), (618, 1936, false), (170, 512, true), (746, 3504, false),
    (2106, 3184, false), (2682, 3040, false), (2234, 1616, false), (2810, 448, false),
    (2062, 2576, true), (2638, 3328, false), (2190, 48, true), (2766, 1824, false),
    (30, 1760, false), (606, 336, false), (158, 3264, false), (734, 2928, false),
    (2094, 688, true), (2670, 1440, false), (2222, 2192, true), (2798, 3968, false),
    (62, 3648, false), (638, 2544, false), (190, 1120, false), (766, 976, false),
    (3, 2128, true), (579, 1504, false), (131, 624, true), (707, 4032, false),
    (2067, 3712, false), (2643, 2352, false), (2195, 1184, false), (2771, 784, false),
    (35, 240, true), (611, 3392, false), (163, 2768, true), (739, 1888, false),
    (2099, 1568, false), (2675, 400, false), (2227, 3072, false), (2803, 2992, false),
    (2055, 736, true), (2631, 2032, false), (2183, 2240, true), (2759, 3536, false),
    (23, 3216, false), (599, 2816, false), (151, 1712, false), (727, 288, false),
    (2087, 2624, true), (2663, 3920, false), (2215, 96, true), (2791, 1392, false),
    (55, 1072, false), (631, 928, false), (183, 3600, false), (759, 2432, false),
    (11, 2160, true), (587, 1472, false), (139, 592, true), (715, 4064, false),
    (2075, 3744, false), (2651, 2320, false), (2203, 1152, false), (2779, 816, false),
    (43, 208, true), (619, 3424, false), (171, 2800, true), (747, 1856, false),
    (2107, 1536, false), (2683, 432, false), (2235, 3104, false), (2811, 2960, false),
    (2063, 704, true), (2639, 2000, false), (2191, 2272, true), (2767, 3568, false),
    (31, 3248, false), (607, 2848, false), (159, 1680, false), (735, 256, false),
    (2095, 2656, true), (2671, 3952, false), (2223, 64, true), (2799, 1360, false),
    (63, 1040, false), (639, 896, false), (191, 3632, false), (767, 2464, false)]

@[expose] def ptil4 (ε : Eps) (s : ℕ) : Array (Array ℕ) :=
  add4 (lift2 (genRows ε s)) (add4 (lift2 (c0Rows ε s)) (lift2 (c0Rows ε s)))

@[expose] def prod4 (ε : Eps) : List ℕ → Array (Array ℕ)
  | [] => one4
  | s :: w => mul4 (ptil4 ε s) (prod4 ε w)

@[expose] def kTil4 : Array (Array ℕ) := prod4 .minus kWord

@[expose] def zIdx : Eps → ℕ
  | .plus => 4
  | .minus => 1

@[expose] def relCheck4 (ε : Eps) : Bool := (extRels ε).all fun w => prod4 ε w == one4

@[expose] def kCheck : Bool :=
  wordRows .minus kWord == kRows && bmul 6 6 kRows kRows == s0Get .minus (zIdx .minus)

@[expose] def sqCheck : Bool :=
  let K1 := add4 one4 kTil4
  let K2 := sub4 one4 kTil4
  let K3 := add4 one4 (mul4 kTil4 kTil4)
  (sqWit.all fun e => mv4 (if e.2.2 then K1 else K2) (dig4 e.2.1) == dig4 e.1) &&
    (List.range 4096).all fun n => !(mv4 K3 (dig4 n) == dig4 0) || sqWit.any fun e => e.1 == n

@[expose] def centerCheck (ε : Eps) : Bool :=
  let T := mulTab ε
  (List.range 64).all fun i =>
    !((List.range 64).all fun j => tabGet T i j == tabGet T j i) || i == 0 || i == zIdx ε

end CFSG.EvenSmallLie.OmegaEight.Chain
