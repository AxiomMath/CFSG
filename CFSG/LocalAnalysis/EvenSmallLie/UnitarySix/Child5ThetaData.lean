module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedgeData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModelData

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaD

@[expose] def PBits : Array ℕ := #[50, 33, 122, 229, 13, 11, 1, 3]

@[expose] def PinvBits : Array ℕ := #[64, 192, 240, 160, 131, 66, 165, 95]

@[expose] def cBits (j : ℕ) : Array ℕ :=
  bmul 8 8 (bmul 8 8 PBits (wedgeGensN.getD j #[])) PinvBits

@[expose] def cWord : List ℕ → Array ℕ
  | [] => id8
  | j :: w => bmul 8 8 (cBits j) (cWord w)

@[expose] def wordA : ℕ → List (Fin 3)
  | 0 => [0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 1]
  | 1 => [0, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 1, 1, 0, 2]
  | 2 => [0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2]
  | 3 => [1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1]
  | _ => [1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 0, 2]

@[expose] def wordB : ℕ → List ℕ
  | 0 => [0, 2, 4, 2]
  | _ => [0, 4, 2, 0, 1, 3, 4, 2, 3]

@[expose] def conjTerm (c : List ℕ) : Array ℕ :=
  bmul 8 8 (bmul 8 8 (cWord c) (cBits 2)) (cWord c.reverse)

@[expose] def termsProd : List (List ℕ) → Array ℕ
  | [] => id8
  | c :: l => bmul 8 8 (conjTerm c) (termsProd l)

@[expose] def eDec : ℕ → List (List ℕ)
  | 0 => [[1]]
  | 1 => [[3]]
  | 2 => [[0], [0, 1]]
  | _ => [[0], []]

@[expose] def nuDec : ℕ → List (List ℕ) × List ℕ
  | 0 => ([[0], [0, 1]], [3, 0, 1, 3])
  | _ => ([[1], []], [3, 1])

@[expose] def thetaCheck : Bool :=
  (bmul 8 8 PBits PinvBits == id8) && (bmul 8 8 PinvBits PBits == id8) &&
  ((List.range 5).all fun j => wordBits (wordA j) == cBits j) &&
  ((List.range 5).all fun j => bmul 8 8 (cBits j) (cBits j) == id8) &&
  (cWord (wordB 0) == genBits 0) && (cWord (wordB 1) == genBits 1) &&
  ((List.range 4).all fun m => termsProd (eDec m) == eBits m) &&
  ((List.range 2).all fun j => bmul 8 8 (termsProd (nuDec j).1) (cWord (nuDec j).2) == nuBits j)

theorem thetaCheck_eq_true : thetaCheck = true := by decide +kernel

end CFSG.EvenSmallLie.UnitarySix.Child5
