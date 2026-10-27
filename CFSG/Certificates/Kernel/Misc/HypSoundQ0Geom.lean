module

public import CFSG.Certificates.Kernel.Misc.LinesPerp
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Certificates.Kernel.Misc.O73Defs
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib

public section

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.KC.Misc.Lines CFSG.KS.PK

private def uPtsLit : List Nat := [5, 9, 13, 17, 20, 33, 36, 49, 52, 65, 68, 80, 85, 89, 93, 101, 105, 109, 117, 121, 125, 129, 132, 144, 149, 153, 157, 165, 169, 173, 181, 185, 189, 193, 196, 208, 213, 217, 221, 229, 233, 237, 245, 249, 253, 257, 260, 272, 277, 281, 285, 293, 297, 301, 309, 313, 317, 320, 325, 329, 333, 337, 340, 353, 356, 369, 372, 389, 393, 397, 401, 404, 417, 420, 433, 436, 453, 457, 461, 465, 468, 481, 484, 497, 500, 513, 516, 528, 533, 537, 541, 549, 553, 557, 565, 569, 573, 576, 581, 585, 589, 593, 596, 609, 612, 625, 628, 645, 649, 653, 657, 660, 673, 676, 689, 692, 709, 713, 717, 721, 724, 737, 740, 753, 756, 769, 772, 784, 789, 793, 797, 805, 809, 813, 821, 825, 829, 832, 837, 841, 845, 849, 852, 865, 868, 881, 884, 901, 905, 909, 913, 916, 929, 932, 945, 948, 965, 969, 973, 977, 980, 993, 996, 1009, 1012, 1025, 1028, 1040, 1045, 1049, 1053, 1061, 1065, 1069, 1077, 1081, 1085, 1088, 1093, 1097, 1101, 1105, 1108, 1121, 1124, 1137, 1140, 1157, 1161, 1165, 1169, 1172, 1185, 1188, 1201, 1204, 1221, 1225, 1229, 1233, 1236, 1249, 1252, 1265, 1268, 1280, 1285, 1289, 1293, 1297, 1300, 1313, 1316, 1329, 1332, 1345, 1348, 1360, 1365, 1369, 1373, 1381, 1385, 1389, 1397, 1401, 1405, 1409, 1412, 1424, 1429, 1433, 1437, 1445, 1449, 1453, 1461, 1465, 1469, 1473, 1476, 1488, 1493, 1497, 1501, 1509, 1513, 1517, 1525, 1529, 1533, 1541, 1545, 1549, 1553, 1556, 1569, 1572, 1585, 1588, 1601, 1604, 1616, 1621, 1625, 1629, 1637, 1641, 1645, 1653, 1657, 1661, 1665, 1668, 1680, 1685, 1689, 1693, 1701, 1705, 1709, 1717, 1721, 1725, 1729, 1732, 1744, 1749, 1753, 1757, 1765, 1769, 1773, 1781, 1785, 1789, 1797, 1801, 1805, 1809, 1812, 1825, 1828, 1841, 1844, 1857, 1860, 1872, 1877, 1881, 1885, 1893, 1897, 1901, 1909, 1913, 1917, 1921, 1924, 1936, 1941, 1945, 1949, 1957, 1961, 1965, 1973, 1977, 1981, 1985, 1988, 2000, 2005, 2009, 2013, 2021, 2025, 2029, 2037, 2041, 2045, 2049, 2052, 2064, 2069, 2073, 2077, 2085, 2089, 2093, 2101, 2105, 2109, 2112, 2117, 2121, 2125, 2129, 2132, 2145, 2148, 2161, 2164, 2181, 2185, 2189, 2193, 2196, 2209, 2212, 2225, 2228, 2245, 2249, 2253, 2257, 2260, 2273, 2276, 2289, 2292, 2304, 2309, 2313, 2317, 2321, 2324, 2337, 2340, 2353, 2356, 2369, 2372, 2384, 2389, 2393, 2397, 2405, 2409, 2413, 2421, 2425, 2429, 2433, 2436, 2448, 2453, 2457, 2461, 2469, 2473, 2477, 2485, 2489, 2493, 2497, 2500, 2512, 2517, 2521, 2525, 2533, 2537, 2541, 2549, 2553, 2557, 2565, 2569, 2573, 2577, 2580, 2593, 2596, 2609, 2612, 2625, 2628, 2640, 2645, 2649, 2653, 2661, 2665, 2669, 2677, 2681, 2685, 2689, 2692, 2704, 2709, 2713, 2717, 2725, 2729, 2733, 2741, 2745, 2749, 2753, 2756, 2768, 2773, 2777, 2781, 2789, 2793, 2797, 2805, 2809, 2813, 2821, 2825, 2829, 2833, 2836, 2849, 2852, 2865, 2868, 2881, 2884, 2896, 2901, 2905, 2909, 2917, 2921, 2925, 2933, 2937, 2941, 2945, 2948, 2960, 2965, 2969, 2973, 2981, 2985, 2989, 2997, 3001, 3005, 3009, 3012, 3024, 3029, 3033, 3037, 3045, 3049, 3053, 3061, 3065, 3069, 3073, 3076, 3088, 3093, 3097, 3101, 3109, 3113, 3117, 3125, 3129, 3133, 3136, 3141, 3145, 3149, 3153, 3156, 3169, 3172, 3185, 3188, 3205, 3209, 3213, 3217, 3220, 3233, 3236, 3249, 3252, 3269, 3273, 3277, 3281, 3284, 3297, 3300, 3313, 3316, 3328, 3333, 3337, 3341, 3345, 3348, 3361, 3364, 3377, 3380, 3393, 3396, 3408, 3413, 3417, 3421, 3429, 3433, 3437, 3445, 3449, 3453, 3457, 3460, 3472, 3477, 3481, 3485, 3493, 3497, 3501, 3509, 3513, 3517, 3521, 3524, 3536, 3541, 3545, 3549, 3557, 3561, 3565, 3573, 3577, 3581, 3589, 3593, 3597, 3601, 3604, 3617, 3620, 3633, 3636, 3649, 3652, 3664, 3669, 3673, 3677, 3685, 3689, 3693, 3701, 3705, 3709, 3713, 3716, 3728, 3733, 3737, 3741, 3749, 3753, 3757, 3765, 3769, 3773, 3777, 3780, 3792, 3797, 3801, 3805, 3813, 3817, 3821, 3829, 3833, 3837, 3845, 3849, 3853, 3857, 3860, 3873, 3876, 3889, 3892, 3905, 3908, 3920, 3925, 3929, 3933, 3941, 3945, 3949, 3957, 3961, 3965, 3969, 3972, 3984, 3989, 3993, 3997, 4005, 4009, 4013, 4021, 4025, 4029, 4033, 4036, 4048, 4053, 4057, 4061, 4069, 4073, 4077, 4085, 4089, 4093]

private def coverIdx : List Nat := [0, 1, 1, 2, 4, 2, 8, 2, 5, 2, 6, 0, 0, 7, 4, 0, 9, 11, 0, 1, 1, 2, 5, 0, 0, 1, 1, 0, 5, 6, 0, 7, 6, 2, 3, 0, 0, 3, 4, 0, 1, 1, 0, 3, 5, 1, 1, 0, 0, 4, 6, 0, 10, 6, 0, 5, 6, 0, 0, 3, 4, 9, 2, 7, 2, 1, 1, 0, 5, 3, 1, 1, 9, 2, 4, 2, 0, 10, 4, 6, 2, 1, 1, 4, 2, 1, 1, 0, 0, 2, 5, 0, 2, 12, 0, 2, 4, 0, 0, 2, 6, 3, 12, 3, 5, 1, 1, 0, 2, 16, 1, 1, 6, 6, 6, 4, 0, 2, 3, 7, 5, 1, 1, 11, 4, 1, 1, 0, 0, 11, 2, 0, 11, 2, 0, 4, 2, 0, 0, 11, 2, 4, 7, 8, 4, 1, 1, 0, 3, 2, 1, 1, 5, 3, 8, 3, 0, 11, 2, 3, 9, 1, 1, 3, 5, 1, 1, 0, 0, 5, 3, 0, 7, 3, 0, 14, 3, 0, 0, 4, 5, 2, 4, 2, 6, 1, 1, 0, 4, 6, 1, 1, 2, 14, 2, 8, 0, 3, 7, 2, 3, 1, 1, 2, 3, 0, 0, 1, 1, 3, 2, 3, 2, 3, 2, 5, 2, 0, 0, 3, 8, 0, 3, 5, 0, 1, 1, 7, 2, 0, 0, 1, 1, 0, 8, 3, 0, 9, 3, 6, 2, 0, 0, 4, 5, 0, 1, 1, 0, 7, 7, 0, 1, 1, 12, 3, 8, 3, 5, 3, 3, 9, 0, 0, 2, 6, 0, 2, 6, 0, 1, 1, 4, 6, 0, 0, 1, 1, 0, 2, 5, 0, 2, 4, 4, 9, 0, 0, 2, 3, 0, 1, 1, 0, 2, 3, 0, 1, 1, 4, 6, 6, 4, 6, 6, 8, 5, 0, 0, 13, 2, 0, 5, 2, 0, 1, 1, 14, 3, 0, 0, 1, 1, 0, 3, 2, 0, 3, 2, 3, 7, 0, 0, 5, 2, 0, 1, 1, 0, 4, 2, 1, 1, 0, 0, 5, 3, 0, 7, 3, 0, 11, 3, 0, 0, 4, 5, 2, 4, 2, 6, 1, 1, 0, 4, 6, 1, 1, 2, 8, 2, 11, 0, 3, 7, 2, 3, 1, 1, 2, 3, 0, 0, 1, 1, 3, 2, 3, 2, 3, 2, 5, 2, 0, 0, 3, 9, 0, 3, 5, 0, 1, 1, 7, 2, 0, 0, 1, 1, 0, 16, 3, 0, 8, 3, 6, 2, 0, 0, 4, 5, 0, 1, 1, 0, 7, 7, 0, 1, 1, 10, 3, 12, 3, 5, 3, 3, 14, 0, 0, 2, 6, 0, 2, 6, 0, 1, 1, 4, 6, 0, 0, 1, 1, 0, 2, 5, 0, 2, 4, 4, 8, 0, 0, 2, 3, 0, 1, 1, 0, 2, 3, 0, 1, 1, 4, 6, 6, 4, 6, 6, 9, 5, 0, 0, 10, 2, 0, 5, 2, 0, 1, 1, 8, 3, 0, 0, 1, 1, 0, 3, 2, 0, 3, 2, 3, 7, 0, 0, 5, 2, 0, 1, 1, 0, 4, 2, 1, 1, 0, 0, 5, 3, 0, 7, 3, 0, 12, 3, 0, 0, 4, 5, 2, 4, 2, 6, 1, 1, 0, 4, 6, 1, 1, 2, 9, 2, 9, 0, 3, 7, 2, 3, 1, 1, 2, 3, 0, 0, 1, 1, 3, 2, 3, 2, 3, 2, 5, 2, 0, 0, 3, 11, 0, 3, 5, 0, 1, 1, 7, 2, 0, 0, 1, 1, 0, 14, 3, 0, 16, 3, 6, 2, 0, 0, 4, 5, 0, 1, 1, 0, 7, 7, 0, 1, 1, 8, 3, 9, 3, 5, 3, 3, 11, 0, 0, 2, 6, 0, 2, 6, 0, 1, 1, 4, 6, 0, 0, 1, 1, 0, 2, 5, 0, 2, 4, 4, 11, 0, 0, 2, 3, 0, 1, 1, 0, 2, 3, 0, 1, 1, 4, 6, 6, 4, 6, 6, 11, 5, 0, 0, 9, 2, 0, 5, 2, 0, 1, 1, 10, 3, 0, 0, 1, 1, 0, 3, 2, 0, 3, 2, 3, 7, 0, 0, 5, 2, 0, 1, 1, 0, 4, 2]

private def moveIdx : List Nat := [1, 3, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 9, 0, 0, 0, 1, 0, 0, 1]

private theorem uPts_eq_uPtsLit : uPts () = uPtsLit.toArray := by
  decide +kernel

private theorem uPts_getElem! (i : Nat) : (uPts ())[i]! = uPtsLit.getD i 0 := by
  rw [uPts_eq_uPtsLit]
  exact list_toArray_getElem! uPtsLit i

private theorem mem_uPts_toList {c : Nat} :
    c ∈ (uPts ()).toList ↔ c < 4096 ∧ isPt c = true := by
  have h : (uPts ()).toList =
      (List.range 4096).filter (fun c => c != 0 && hermC c c == 0 && normC c == c) := by
    simp [uPts, List.toList_toArray]
  rw [h, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hc, hpred⟩
    refine ⟨hc, (isPt_iff c).2 ?_⟩
    simpa only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] using hpred
  · rintro ⟨hc, hpt⟩
    refine ⟨hc, ?_⟩
    simpa only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] using (isPt_iff c).1 hpt

private theorem uPts_toList_sortedLT : (uPts ()).toList.SortedLT := by
  have h : (uPts ()).toList =
      (List.range 4096).filter (fun c => c != 0 && hermC c c == 0 && normC c == c) := by
    simp [uPts, List.toList_toArray]
  rw [List.sortedLT_iff_pairwise, h]
  exact List.Pairwise.filter _ List.pairwise_lt_range

private theorem UL_sortedLT {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) :
    UL.SortedLT := by
  have hlen : UL.length = 693 := H.len
  rw [List.sortedLT_iff_pairwise, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := H.mono i j hij (by omega)
  simpa [List.getD_eq_getElem?_getD, hi, hj] using this

private theorem mem_UL_iff {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) {c : Nat} :
    c ∈ UL ↔ c < 4096 ∧ isPt c = true := by
  constructor
  · intro hc
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hc
    have hi' : i < 693 := by rw [H.len] at hi; exact hi
    have hlt : UL[i] < 4096 := by
      have h := H.lt i hi'
      simpa [List.getD_eq_getElem?_getD, hi] using h
    have hpt : isPt (UL[i]) = true := by
      have h := H.pt i hi'
      simpa [List.getD_eq_getElem?_getD, hi] using h
    rw [← e]
    exact ⟨hlt, hpt⟩
  · rintro ⟨hc, hpt⟩
    rcases H.pos c hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hlen : UL.length = 693 := H.len
      have hy : fd 10 PP c < UL.length := by omega
      have he : UL[fd 10 PP c] = c := by
        rw [List.getElem_eq_getD 0, ← H.fd12 _ h1, h2]
      rw [← he]
      exact List.getElem_mem _
    · exact absurd hpt h2

open scoped CFSG.Decide.Bounded in
private theorem cover_check :
    ∀ z ∈ List.range 693, 0 < z →
      coverIdx.getD z 0 < 31 ∧
      hermC (uPtsLit.getD z 0) (uPtsLit.getD (23 * coverIdx.getD z 0) 0) = 0 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem move_check :
    ∀ k ∈ List.range 31,
      moveIdx.getD k 0 < 693 ∧
      hermC (uPtsLit.getD (moveIdx.getD k 0) 0) (uPtsLit.getD (23 * k) 0) ≠ 0 := by
  decide +kernel

theorem pts_eq_uPts_toList {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) :
    UL = (uPts ()).toList := by
  refine List.SortedLT.eq_of_mem_iff (UL_sortedLT H) uPts_toList_sortedLT (fun c => ?_)
  exact (mem_UL_iff H (c := c)).trans (mem_uPts_toList (c := c)).symm

theorem uPts_cover_centers : ∀ z < 693, 0 < z → ∃ k < 31,
    hermC ((uPts ())[z]!) ((uPts ())[23 * k]!) = 0 := by
  intro z hz hz0
  obtain ⟨hk, hh⟩ := cover_check z (List.mem_range.mpr hz) hz0
  refine ⟨coverIdx.getD z 0, hk, ?_⟩
  rw [uPts_getElem! z, uPts_getElem! (23 * coverIdx.getD z 0)]
  exact hh

theorem uPts_move_centers : ∀ k < 31, ∃ p < 693,
    hermC ((uPts ())[p]!) ((uPts ())[23 * k]!) ≠ 0 := by
  intro k hk
  obtain ⟨hp, hh⟩ := move_check k (List.mem_range.mpr hk)
  refine ⟨moveIdx.getD k 0, hp, ?_⟩
  rw [uPts_getElem! (moveIdx.getD k 0), uPts_getElem! (23 * k)]
  exact hh

end CFSG.KC.Misc.Hyp

end
