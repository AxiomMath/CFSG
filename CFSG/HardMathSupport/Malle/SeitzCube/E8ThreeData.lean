module

public import CFSG.HardMathSupport.Malle.SeitzCube.E8PhiSixData

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration Polynomial
open scoped Matrix

@[expose] def e8W3Word : List (Fin Tag.E8.rank) :=
  [6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 0]

@[expose] def e8W3Mat : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 0, 0, 2], [-1, 2, 0, 0, -1, 0, 0, 2], [0, 2, -1, 1, -2, 0, 0, 3], [0, 4, -1, 0, -2, 0, 0, 4], [0, 3, 0, 0, -2, 0, 0, 3], [0, 2, 0, 0, -1, -1, 1, 2], [0, 1, 0, 0, 0, -1, 0, 2], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8W3Basis : List (List ℤ) :=
  [[1, 0, 0, 0, -1, 0, 1, 0], [1, 0, 0, 0, -1, 0, 0, 0], [0, 0, -1, 2, -1, 1, 0, 0], [0, 2, 1, 1, 0, -1, 0, 0], [1, 1, 0, 0, -1, -1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [-1, 1, 1, -1, 1, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8W3BasisInv : List (List ℤ) :=
  [[0, 1, -1, 1, -1, -1, -1, 0], [0, 3, 0, 1, -2, -2, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, -2, 0, 0, 1, 1, -1, 0], [0, 0, -1, 1, -1, -1, -1, 0], [0, 4, 0, 1, -3, -2, 1, 0], [1, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxRecDepth 100000 in
theorem e8W3_wordMat :
    wordMat Tag.E8 e8W3Word = toMat Tag.E8.rank e8W3Mat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8W3_pow : (wordMat Tag.E8 e8W3Word) ^ 3 = 1 := by
  rw [e8W3_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8W3_charpoly :
    (wordMat Tag.E8 e8W3Word).charpoly =
      ([3, 3, 3, 1, 1].map fun d => cyclotomic d ℤ).prod := by
  rw [e8W3_wordMat]
  exact charpoly_of_basis e8W3Mat e8W3Basis e8W3BasisInv [3, 3, 3, 1, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem e8W3_mulVec_theta : (wordMat Tag.E8 e8W3Word) *ᵥ e8Theta = e8Theta := by
  rw [e8W3_wordMat]
  decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube
