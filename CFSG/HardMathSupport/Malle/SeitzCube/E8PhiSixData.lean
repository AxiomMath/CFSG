module

public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration Polynomial
open scoped Matrix

@[expose] def e8W6Word : List (Fin Tag.E8.rank) :=
  [5, 4, 3, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 1, 3, 1]

@[expose] def e8W6Mat : List (List ℤ) :=
  [[0, -1, 0, 0, 1, 0, 0, 0], [1, -2, 0, 0, 1, 0, 0, 1], [0, -2, 1, -1, 2, 0, 0, 1], [0, -4, 1, 0,
  2, 0, 0, 2], [0, -3, 0, 0, 2, 0, 0, 2], [0, -2, 0, 0, 1, 1, -1, 2], [0, -1, 0, 0, 0, 1, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8W6Basis : List (List ℤ) :=
  [[-1, 0, -1, 0, -1, 0, 0, 0], [-1, 0, -1, 0, -1, 0, 1, 0], [-1, 0, 0, 0, 1, 0, 0, 0], [-1, 1, 0,
  2, 1, 3, 0, 0], [-1, 1, -1, 1, -1, 1, 0, 0], [-1, -1, -1, -1, 0, 0, 0, 0], [1, 0, 1, 0, 1, 1, 0,
  0], [0, 0, 0, 0, 0, 0, 2, 1]]

@[expose] def e8W6BasisInv : List (List ℤ) :=
  [[-3, 0, -1, 0, 1, 1, -1, 0], [-1, 0, 1, -1, 2, 0, 1, 0], [5, 0, 1, 0, -2, -2, 2, 0], [-1, 0, -1,
  1, -1, 0, -2, 0], [-3, 0, 0, 0, 1, 1, -1, 0], [1, 0, 0, 0, 0, 0, 1, 0], [-1, 1, 0, 0, 0, 0, 0,
  0], [2, -2, 0, 0, 0, 0, 0, 1]]

theorem e8W6_wordMat :
    wordMat Tag.E8 e8W6Word = toMat Tag.E8.rank e8W6Mat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8W6_pow : (wordMat Tag.E8 e8W6Word) ^ 6 = 1 := by
  rw [e8W6_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8W6_charpoly :
    (wordMat Tag.E8 e8W6Word).charpoly =
      ([6, 6, 6, 1, 2].map fun d => cyclotomic d ℤ).prod := by
  rw [e8W6_wordMat]
  exact charpoly_of_basis e8W6Mat e8W6Basis e8W6BasisInv [6, 6, 6, 1, 2]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

@[expose] def e8Theta : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem e8Theta_mem : e8Theta ∈ rootFinset .E8 := by decide +kernel

theorem e8W6_mulVec_theta : (wordMat Tag.E8 e8W6Word) *ᵥ e8Theta = e8Theta := by
  rw [e8W6_wordMat]
  decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube
