module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
public import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import Std.Data.HashSet
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
public meta import Std.Data.HashSet
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native

set_option compiler.extract_closed false

@[expose] def yPows : Array (Array Nat) := (List.range 6).toArray.map (pw yA)

@[expose] def yConjT (v : Array Nat) (a : Nat) : Array Nat :=
  compA 3510 yPows[a]! (compA 3510 v yPows[5 - a]!)

@[expose] def p24 (v : Array Nat) : Array Nat :=
  let v3 := compA 3510 v (compA 3510 v v)
  let v6 := compA 3510 v3 v3
  let v12 := compA 3510 v6 v6
  compA 3510 v12 v12

@[expose] def star5W1 (v : Array Nat) : Array Nat :=
  compA 3510 (yConjT v 0) (compA 3510 (yConjT v 1) (compA 3510 (yConjT v 2) (yConjT v 3)))

@[expose] def star5W2 (v : Array Nat) : Array Nat :=
  compA 3510 (yConjT v 0) (compA 3510 (yConjT v 0) (compA 3510 (yConjT v 1) (yConjT v 4)))

@[expose] def star5OK (v : Array Nat) : Bool :=
  eqA 3510 v (idA 3510) || !(eqA 3510 (p24 v) (idA 3510)) ||
    !(eqA 3510 (p24 (star5W1 v)) (idA 3510)) || !(eqA 3510 (p24 (star5W2 v)) (idA 3510))

@[noinline, expose] def star5Check : Bool :=
  allLt centClosure.1.size fun i => star5OK centClosure.1[i]!

@[expose] def zw : List Int :=
  [-2, -2, -2, -2, -1, -2, -1, -2, -2, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -2, -2, -1,
   -2, -1, -2, -1, 2, 1, 2, 2, -1, -2, -2, -2, -2, -2, -2, -2, -2, -1, -2, -2, -2, -2, -2, 1, 2,
   2, -1, 2, -1, -2, -2, -2, -2, -1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, -2, -2, -2, 1, 2, 2, 1, -2,
   -2, 1, -2, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, -2, -2, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 2, 2,
   2, 2, 2, 2, 2, -1, -2, 1, -2, 1, 2, 1, 2, 1, -2, -2, -2, -2, 1, 2, 2, 2, 2, 1, -2, -2, -2,
   -2, -2, -2, 1, 2, 2, 1, -2, 1, -2, -2, -2, -2, -1, -2, -2, -2, -2, -1, -2, -2, -2, -2, -1,
   -2, -2, -1, -2, -2, -2, -1, 2, 2, 2, -1, -2, -2, -2, -1, -2, -1, -2, -1, 2, -1, 2, 2, 2, 2,
   2, 2, 1, -2, -2, -1, -2, -2, -2, -1, 2, 2, 2, 2, -1, -2, -1, -2, -2, -2, -2, -1, -2, -1, 2,
   -1, 2, 2, 2, 2, 2, 2, 1, -2]

@[expose] def zA : Array Nat := evalW zw

@[expose] def gens6A : Array (Array Nat) := #[xA, yA, hA, n1A, n2A, zA]

@[expose] def gens6Inv : Array (Array Nat) := gens6A.map (invCand 3510)

@[expose] def sixW (w : List Int) : Array Nat := wordA 3510 gens6A gens6Inv w

@[expose] def g1w : List Int := [5, 3, 4, 4, 4, -1]

@[expose] def g2w : List Int := [2, 5, 3, -6, 2, 1]

@[expose] def g1A : Array Nat := sixW g1w

@[expose] def g2A : Array Nat := sixW g2w

@[expose] def orbGens : Array (Array Nat) := #[g1A, g2A]

@[expose] def orbGensInv : Array (Array Nat) := orbGens.map (invCand 3510)

@[noinline, expose] def genCheck : Bool :=
  lettersOK 2 zw && eqA 3510 (compA 3510 zA xA) (compA 3510 (pw xA 2) zA) &&
    lettersOK 6 g1w && lettersOK 6 g2w &&
    allLt 6 (fun k => isInvA 3510 gens6A[k]! gens6Inv[k]!)

@[expose] def imgA (g : Array Nat) (a : Array Nat) : Array Nat := a.map fun p => g[p]!

@[expose] def mix64 (x : Nat) : Nat :=
  let m := 18446744073709551616
  let x := (x ^^^ (x >>> 30)) * 13787848793156543929 % m
  let x := (x ^^^ (x >>> 27)) * 10723151780598845931 % m
  x ^^^ (x >>> 31)

@[expose] def hashTab : Array Nat :=
  (List.range 3510).toArray.map fun p =>
    mix64 ((p + 1) * 11400714819323198485 % 18446744073709551616) % 9007199254740992

@[expose] def hashA (a : Array Nat) : Nat := a.foldl (fun h p => h + hashTab[p]!) 0

@[expose] def hashImg (g a : Array Nat) : Nat := a.foldl (fun h p => h + hashTab[g[p]!]!) 0

@[expose] def orbSearchA (gens : Array (Array Nat)) (start : Array Nat) (bound : Nat) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut sets : Array (Array Nat) := #[start]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert (hashA start)
  let mut head := 0
  for _ in [0:bound] do
    if head < sets.size && sets.size < bound then
      let s := sets[head]!
      for k in [0:gens.size] do
        if sets.size < bound then
          let h := hashImg gens[k]! s
          if !seen.contains h then
            seen := seen.insert h
            sets := sets.push (imgA gens[k]! s)
            par := par.push head
            lab := lab.push k
      head := head + 1
  return (sets, par, lab)

@[expose] def translatesA (gens : Array (Array Nat)) (start : Array Nat)
    (sets : Array (Array Nat)) (par lab : Array Nat) : Bool :=
  decide (0 < sets.size) && sets[0]! == start &&
    allLt sets.size fun k => k == 0 || (decide (par[k]! < k) && decide (lab[k]! < gens.size) &&
      sets[k]! == imgA gens[lab[k]!]! sets[par[k]!]!)

@[expose] def distinctNat (l : List Nat) : Bool :=
  strictIncr (l.mergeSort fun a b => decide (a ≤ b))

@[expose] def pointListOK (n : Nat) (l : List Nat) : Bool :=
  l.all (fun q => decide (q < n)) && strictIncr l

@[expose] def orbitPartA (gens : Array (Array Nat)) (start : Array Nat) (size : Nat) :
    Bool × List Nat :=
  let r := orbSearchA gens start size
  (translatesA gens start r.1 r.2.1 r.2.2 && r.1.size == size, r.1.toList.map hashA)

@[expose] def h1w : List Int :=
  [-1, -1, -2, -1, -2, -2, -1, -2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1]

@[expose] def h2w : List Int :=
  [-1, -1, -2, -1, -1, -1, -2, -1, -2, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1]

@[expose] def h1A : Array Nat := wordA 3510 orbGens orbGensInv h1w

@[expose] def h2A : Array Nat := wordA 3510 orbGens orbGensInv h2w

@[expose] def hchainW : Array (List Int) :=
  #[[], [],
   [1, 1, 1, -2, 1, 2, 2, 2, -1, 2, 2, 1, 1, 2, 1, 1, -2, -2, 1, 2, 1, -2, 1, -2, 1, 1, 1, -2,
    -1, -1, 2, 2, 1, -2, -1, 2],
   [1, 2, 1, -2, -2, 1, 1, -2, -2, -2, 1, -2, 1, 2, -1, -2, -1, 2, 1, 1, -2],
   [-2, -1, -2, -2, -1, 2, 2, 1, -2, -1, -1, -2, -1, 2, 1, 1, -2, -1, 2, 2, 1, -2, 1, 1, -2, -1],
   [1, 2, -1, -1, 2, -1, -2, -2, 1, -2, 1, 2, -1, -2, -2, 1, 1, 2, -1, -1, -1, 2, 1, 2, 2, -1,
    2, 2, 2, -1, 2, 1, -2, -2, 1, 2, 1, 2, -1, -2, -1],
   [1, 2, -1, -1, 2, -1, -2, -2, 1, 1, -2, -2, -2, 1, -2, -1, -2, -1, -2, -2, -2, -1, -1, -2,
    -2, -2, -1, -2, -2],
   [1, 1, 1, -2, 1, 2, 2, 2, -1, -1, -2, -2, 1, -2, -1, 2, 1, 1, 2, 2, 1, 2, 1, 2, -1, 2, 2, 2,
    -1],
   [1, 2, -1, -1, 2, -1, -2, -2, 1, -2, 1, 2, -1, -2, -2, 1, 1, 2, -1, -1, -1, -1, 2, 1, 1, -2,
    1, -2, -1, 2, -1, 2, 1, 1, 1],
   [1, 2, -1, -1, 2, -1, -2, -2, 1, 1, 2, 2, -1, 2, 2, 2, -1, -2, -2, 1, -2, -1, -2, -1, -2,
    -2, -1, 2, 2, 1, 1, 2, 2]]

@[expose] def hchainBase : Array Nat := #[85, 86, 162, 102, 401, 1440, 457]

@[expose] def hchainS : Array (Array Nat) :=
  (List.range 8).foldl (fun S j =>
    S.push (wordA 3510 S (S.map (invCand 3510)) (hchainW.getD (j + 2) []))) #[h1A, h2A]

@[noinline, expose] def chainCheck : Bool :=
  allLt 2 (fun k => isInvA 3510 orbGens[k]! orbGensInv[k]!) &&
    h1A[0]! == 0 && h2A[0]! == 0 && lettersOK 2 h1w && lettersOK 2 h2w &&
    rawChainOK 3510 (hchainS.extract 0 2) hchainS hchainBase hchainW 4 &&
    (rawOrbitSizes 3510 hchainS hchainBase).prod == 2903040 &&
    (let p := orbitPartA orbGens #[0] 360
     p.1 && distinctNat p.2)

@[expose] def s0List : List Nat :=
  [0, 4, 13, 20, 24, 45, 48, 49, 50, 58, 65, 77, 78, 85, 86, 102, 127, 150, 154, 162, 172, 184,
   185, 187, 204, 220, 224, 232, 240, 247, 248, 255, 259, 262, 263, 275, 296, 308, 329, 332,
   333, 341, 364, 401, 412, 416, 440, 441, 443, 457, 469, 471, 481, 491, 492, 500, 523, 534,
   535, 536, 559, 563, 576, 583, 585, 602, 603, 620, 663, 668, 683, 704, 711, 717, 719, 720,
   721, 752, 763, 764, 771, 777, 779, 788, 793, 800, 810, 818, 819, 825, 844, 846, 847, 854,
   879, 890, 894, 904, 921, 936, 939, 949, 964, 991, 998, 1001, 1003, 1009, 1010, 1018, 1022,
   1034, 1036, 1037, 1040, 1045, 1053, 1059, 1064, 1066, 1073, 1074, 1078, 1081, 1087, 1096,
   1111, 1113, 1139, 1142, 1143, 1162, 1163, 1189, 1194, 1212, 1258, 1263, 1265, 1269, 1271,
   1282, 1297, 1306, 1330, 1342, 1355, 1365, 1366, 1382, 1383, 1403, 1411, 1422, 1425, 1426,
   1431, 1439, 1440, 1459, 1471, 1474, 1482, 1502, 1517, 1526, 1531, 1532, 1574, 1587, 1590,
   1594, 1637, 1641, 1646, 1672, 1679, 1688, 1692, 1700, 1712, 1713, 1717, 1718, 1728, 1786,
   1790, 1807, 1809, 1858, 1859, 1866, 1870, 1873, 1882, 1889, 1897, 1923, 1926, 1950, 1953,
   1967, 1972, 1985, 1995, 2013, 2015, 2020, 2030, 2033, 2056, 2071, 2073, 2074, 2077, 2089,
   2093, 2096, 2106, 2110, 2126, 2149, 2159, 2168, 2172, 2178, 2182, 2206, 2208, 2211, 2212,
   2224, 2234, 2236, 2244, 2261, 2271, 2298, 2302, 2336, 2347, 2363, 2365, 2376, 2385, 2388,
   2393, 2405, 2409, 2428, 2439, 2444, 2475, 2481, 2501, 2507, 2520, 2524, 2525, 2526, 2542,
   2546, 2548, 2557, 2563, 2567, 2569, 2575, 2576, 2582, 2584, 2596, 2606, 2613, 2628, 2664,
   2671, 2677, 2716, 2743, 2746, 2751, 2754, 2762, 2767, 2782, 2783, 2784, 2790, 2792, 2807,
   2822, 2827, 2840, 2841, 2845, 2846, 2880, 2899, 2900, 2933, 2952, 2956, 2962, 2969, 2970,
   2972, 2979, 2989, 2995, 2996, 3003, 3010, 3031, 3039, 3041, 3042, 3055, 3078, 3094, 3115,
   3124, 3128, 3146, 3152, 3164, 3175, 3176, 3189, 3190, 3201, 3204, 3226, 3228, 3230, 3232,
   3247, 3276, 3283, 3285, 3286, 3287, 3294, 3305, 3309, 3313, 3314, 3330, 3360, 3368, 3371,
   3379, 3402, 3417, 3428, 3432, 3447, 3453, 3465, 3507]

@[expose] def s0Arr : Array Nat := s0List.toArray

@[expose] def st1Arr : Array Nat := imgA (evalW [1]) s0Arr

@[expose] def st2Arr : Array Nat := imgA (evalW [2]) s0Arr

@[expose] def st3Arr : Array Nat := imgA (evalW [2, 1]) s0Arr

@[noinline, expose] def orbitsCheck : Bool :=
  let p0 := orbitPartA orbGens s0Arr 1
  let p1 := orbitPartA orbGens st1Arr 1575
  let p2 := orbitPartA orbGens st2Arr 22400
  let p3 := orbitPartA orbGens st3Arr 37800
  pointListOK 3510 s0List && imgSorted g1A s0List == s0List && imgSorted g2A s0List == s0List &&
    p0.1 && p1.1 && p2.1 && p3.1 && distinctNat (p0.2 ++ p1.2 ++ p2.2 ++ p3.2)

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
