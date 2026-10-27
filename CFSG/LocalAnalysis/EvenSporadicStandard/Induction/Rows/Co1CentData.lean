module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSpinCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairData

public section

namespace CFSG.EvenSporadicStandard.Co1Cent

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin CFSG.EvenSporadicStandard.Co1Pair
  CFSG.Sporadic.Co1Block

@[expose] def centNums : Array Nat :=
  ((include_str "Co1CentTbl.txt").splitOn " ").filterMap (fun s => s.trimAscii.toNat?) |>.toArray

@[expose] def readWordsD (a : Array Nat) : Nat → Nat → List (List Int)
  | 0, _ => []
  | m + 1, p =>
    ((List.range a[p]!).map fun i => decLetter a[p + 1 + i]!) :: readWordsD a m (p + 1 + a[p]!)

@[expose] def sWords : List (List Int) := readWordsD centNums 6 0

@[expose] def sRows : List Rows := sWords.map (word [cpX, cpY] [inv cpX, inv cpY])

@[expose] def sInv : List Rows := sRows.map inv

@[expose] def centData : SpinData where
  d := 24
  rs := sRows
  is := sInv
  v0 := 5433013
  bw := [[], [1], [2], [3], [-3], [4], [5], [-5], [6], [-6], [2, 1], [3, 1], [-3, 1], [4, 1],
    [5, 1], [-5, 1], [6, 1], [-6, 1], [1, 2], [3, 2], [5, 2], [-5, 2], [6, 2], [1, 3]]
  C := #[11182118, 6768434, 4487844, 14954503, 14959925, 131399, 15126974, 6528651, 533405,
    8475752, 2188071, 1199673, 1997282, 12468996, 8780290, 2761876, 3027528, 6521116, 6534806,
    719605, 3301409, 1511849, 9128858, 16036633]
  sel := [(0, 4, 0), (0, 4, 1), (0, 4, 2), (0, 4, 3), (0, 4, 4), (0, 4, 5), (0, 4, 6),
    (0, 4, 7), (0, 4, 8), (0, 4, 9), (0, 4, 10), (0, 4, 11), (0, 4, 12), (0, 4, 13), (0, 4, 14),
    (0, 4, 15), (0, 4, 16), (0, 4, 17), (0, 4, 18), (0, 4, 19), (0, 4, 20), (0, 4, 21),
    (0, 4, 22), (0, 4, 23)]
  lam := #[0, 0, 0, 257004, 0, 0, 101345, 0, 38573, 35859, 114585, 224294, 82849, 96233, 199973,
    1384, 71689, 42756, 198555, 5953, 175523, 62427, 166285, 18780]
  wcols := [3180873, 6710538, 11822092, 6512720, 13484064, 7908224]
  pcoords := [0, 1, 2, 4, 5, 7]

@[expose] def centOK : Bool :=
  sWords.length == 6 && mul cpX (inv cpX) == one && mul cpY (inv cpY) == one && spinOK centData

@[expose] def cx (x : Nat) : Rows := centData.mx x

@[expose] def gdX : List Nat := [3, 9, 10, 18, 24, 27, 37, 44, 47, 52, 61, 62]

@[expose] def singRecs : List (Nat × Nat) := [(0, 1), (4, 11646465), (11, 11646465),
  (15, 8388609), (17, 11646465), (21, 8388609), (26, 8388609), (30, 11646465), (34, 11646465),
  (38, 11646465), (41, 11646465), (45, 11646465), (51, 11646465), (55, 11646465), (56, 11646465),
  (60, 11646465)]

@[expose] def exclRecs : List (Nat × Nat × Nat) := [(1, 1, 1), (2, 3, 1), (5, 1, 1),
  (6, 3, 1), (7, 3, 1), (8, 3, 1), (12, 3, 1), (13, 3, 1), (14, 1, 1), (16, 1, 1), (19, 3, 1),
  (20, 1, 1), (22, 3, 1), (23, 3, 1), (25, 3, 1), (28, 3, 1), (29, 3, 1), (31, 1, 1), (32, 3, 1),
  (33, 3, 1), (35, 1, 1), (36, 3, 1), (39, 1, 1), (40, 1, 1), (42, 3, 1), (43, 3, 1), (46, 3, 1),
  (48, 3, 1), (49, 3, 1), (50, 1, 1), (53, 3, 1), (54, 1, 1), (57, 1, 1), (58, 3, 1), (59, 3, 1),
  (63, 3, 1)]

@[expose] def gdRows : List Rows := gdX.map cx

@[expose] def triTrivial (Ct : Array Nat) : Bool :=
  twoBTris.all fun p =>
    let a := vecMulN 24 Ct p.1
    a == p.1 || a == p.2 || a == (p.1 ^^^ p.2)

@[expose] def singOK (x u : Nat) : Bool :=
  decide (u ≠ 0) && decide (u < 2 ^ 24) && act (cx x) u == 0

@[expose] def exclOK (x e u : Nat) : Bool :=
  let c := pow (cx x) e
  mul c aR == mul aR c && triTrivial (transposeRows 24 c) &&
    decide (act cpX (act c u) < 2 ^ 24) && decide (act c (act cpX u) < 2 ^ 24) &&
    act cpX (act c u) != act c (act cpX u)

@[expose] def classOK : Bool :=
  centData.wcols.length == 6 && gdX.length == 12 && gdX.all (· < 64) &&
    gdRows.all (fun G => validR 24 G && validR 24 (inv G)) &&
    gdRows.all (fun G => mul G (inv G) == one) &&
    gdRows.all (fun G => mul G G == one || mul (mul G G) G == one) &&
    gdRows.all (fun G => gdRows.all fun H =>
      !(mul G G == one && mul H H == one) || mul G H == mul H G) &&
    decide ((gdRows.filter fun G => mul G G == one).length ≤ 4) &&
    gdRows.all (fun G => gdRows.all fun H =>
      let c := mul (mul (mul G H) (inv G)) (inv H)
      mul c c == one) &&
    (List.range 64).all (fun x => gdX.contains x ||
      singRecs.any (fun r => r.1 == x && singOK x r.2) ||
      exclRecs.any (fun r => r.1 == x && exclOK x r.2.1 r.2.2))

end CFSG.EvenSporadicStandard.Co1Cent
