module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.LargeExtraspecial.DW.Insp

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native

@[expose] def eWords : List (List ℤ) :=
  [[2, 1, 11, 13, 9, 12, 16, 17, 5, 14, 7, 15, 11, 16],
    [15, 13, 9, 12, 16, 17, 5, 14, 7, 16],
    [10, 8, 12, 3, 9, 12, 4, 9, 5, 10, 7, 11],
    [7, 8, 6, 5]]

@[expose] def bwEntries : List (List ℕ × ℕ × List ℤ × ℕ × ℕ) :=
  [([0], 0, [], 0, 1), ([0, 1], 0, [], 1, 1),
    ([0, 1, 1], 0, [10, 8, 12, 3, 9, 12, 4, 16, 17, 16], 1, 2),
    ([0, 2, 3], 0, [16, 8, 3, 11, 13, 4, 9, 11, 16], 2, 1),
    ([0, 2, 3, 2, 3], 0, [16, 8, 3, 11, 13, 4, 9, 15, 16], 2, 2),
    ([0, 1, 2, 3], 2, [12, 4, 2, 3, 13, 6, 12, 9, 14, 7], 0, 1),
    ([0, 1, 2, 3, 1, 2, 3], 1, [14, 3, 1, 13, 6, 16, 13, 17, 9, 14, 7, 16], 0, 2),
    ([0, 1, 2, 3, 2, 3], 2,
      [14, 2, 1, 3, 1, 12, 17, 6, 13, 4, 16, 17, 9, 14, 10, 15, 11, 16], 0, 1),
    ([0, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3], 1, [5, 6, 17, 12, 5, 15, 11, 16], 0, 2),
    ([1], 0, [2, 15, 11], 0, 1),
    ([2, 3], 0, [14, 10, 1, 3, 1, 15, 13, 6, 15, 9, 13, 12, 16, 17, 7, 11, 16], 1, 1),
    ([1, 2, 3], 0, [17, 12, 2, 3, 12, 17], 2, 1),
    ([1, 2, 3, 2, 3], 0, [17, 12, 2, 3, 12, 17, 15, 11], 2, 2),
    ([0, 2], 0, [13, 6, 3, 13, 16, 13, 4, 17, 14, 7, 15, 11, 16], 1, 1),
    ([0, 2, 2], 0, [13, 6, 3, 13, 16, 13, 4, 17, 14, 7, 16], 1, 2), ([0, 1, 2], 0, [], 2, 1),
    ([0, 1, 2, 1, 2], 0, [16, 17, 9, 14, 7, 15, 11, 16], 2, 2),
    ([0, 1, 2, 2], 0, [15, 11], 2, 2),
    ([0, 1, 2, 2, 1, 2, 2], 0, [10, 8, 12, 3, 9, 12, 4, 16, 17, 16], 2, 2),
    ([2], 0, [14, 10, 1, 3, 1, 4, 8, 6, 13, 12, 4, 14, 10], 0, 1),
    ([1, 2], 0, [14, 10, 1, 3, 1, 4, 8, 6, 13, 12, 4, 14, 10], 1, 1),
    ([1, 2, 2], 0, [14, 10, 1, 3, 1, 4, 8, 6, 13, 12, 4, 14, 10, 15, 11], 1, 2),
    ([0, 0, 1, 1], 0, [], 1, 2),
    ([0, 0, 1, 1, 0, 1, 1], 0, [2, 15, 11], 0, 1),
    ([0, 0, 1, 1, 2], 0, [15, 11], 2, 1),
    ([0, 0, 1, 1, 2, 0, 1, 1, 2], 0, [14, 10, 1, 3, 1, 4, 8, 6, 13, 12, 4, 14, 10, 15, 11], 1, 2),
    ([0, 0, 1, 1, 2, 2], 0, [], 2, 2),
    ([0, 0, 1, 1, 2, 2, 0, 1, 1, 2, 2], 0, [14, 10, 1, 3, 1, 4, 8, 6, 13, 12, 4, 14, 10], 1, 1),
    ([0, 1, 1, 2], 0, [10, 8, 12, 3, 9, 12, 4, 16, 17, 16], 2, 2),
    ([0, 1, 1, 2, 2], 0, [16, 17, 9, 14, 7, 15, 11, 16], 2, 2)]

@[expose] def invData : List (List ℤ × List ℤ × ℕ) :=
  [([10, 5, 3, 2, 1, 7, 8, 15, 13, 9, 12, 5, 15], [2, 17, 12, 16, 17, 9, 7, 11], 1),
    ([14, 3, 2, 1, 17, 6, 3, 11, 13, 9, 12, 10, 15, 11],
      [5, 3, 2, 1, 6, 13, 6, 11, 13, 9, 12, 10, 15, 11], 0),
    ([3, 10, 1, 7, 4, 8, 6, 12, 17, 12, 4, 5, 7, 15], [13, 2, 1, 12, 11, 13, 9, 5, 7, 15, 11, 16],
      0)]

@[expose] def aArr (i : ℕ) : Array ℕ := omegaW (eWords.getD i [])

@[expose] def termArr (t : List ℕ) : Array ℕ :=
  t.foldr (fun i u => compA 360 (aArr i) u) (idA 360)

@[expose] def repTerms : List (List ℕ) := [[0], [0, 1], [0, 1, 2]]

@[expose] def bwConj (k : ℕ) (w : List ℤ) : Array ℕ := compA 360 (omegaW w) (powArr genArrs[8]! k)

@[expose] def relCheck : Bool :=
  eqA 360 (powArr genArrs[8]! 3) (idA 360) &&
    eqA 360 (compA 360 genArrs[9]! genArrs[9]!) (idA 360) &&
    eqA 360 (compA 360 genArrs[9]! genArrs[8]!) (compA 360 (powArr genArrs[8]! 2) genArrs[9]!)

@[expose] def eCheck : Bool :=
  (List.range 4).all (fun i => eqA 360 (powArr (aArr i) 3) (idA 360) &&
      (List.range 4).all fun j => commArr (aArr i) (aArr j)) &&
    !eqA 360 (termArr [0, 1, 2]) (idA 360) &&
    commArr genArrs[9]! (aArr 0) && commArr genArrs[9]! (aArr 1)

@[expose] def bwCheck : Bool :=
  bwEntries.all fun e =>
    eqA 360 (compA 360 (bwConj e.2.1 e.2.2.1) (termArr e.1))
      (compA 360 (powArr (termArr (repTerms.getD e.2.2.2.1 [])) e.2.2.2.2)
        (bwConj e.2.1 e.2.2.1))

@[expose] def invCheck : Bool :=
  (List.range 3).all fun i =>
    eqA 360 (compA 360 (omegaW (invData.getD i ([], [], 0)).1)
        (omegaW (invData.getD i ([], [], 0)).2.1))
      (compA 360 (termArr (repTerms.getD (invData.getD i ([], [], 0)).2.2 []))
        (omegaW (invData.getD i ([], [], 0)).1)) &&
    eqA 360 (compA 360 (mainArrs.getD i #[]) (compA 360 (omegaW (invData.getD i ([], [], 0)).2.1)
        (compA 360 (mainArrs.getD i #[]) (omegaW (invData.getD i ([], [], 0)).2.1)))) (idA 360)

@[expose] def dw27Check : Bool := relCheck && eCheck && bwCheck && invCheck

end CFSG.LargeExtraspecial.DW.Insp
