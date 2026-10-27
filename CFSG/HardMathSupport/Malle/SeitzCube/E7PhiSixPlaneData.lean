module

public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration Polynomial
open scoped Matrix

@[expose] def e7W6Word : List (Fin Tag.E7.rank) := [4, 5, 3, 4, 1, 3, 1, 2, 6, 3]

@[expose] def e7W6Mat : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [1, 0, -1, 0, 1, 0, 0], [1, 1, 0, -1, 1, 0, 0],
    [2, 1, -1, -1, 1, 1, 0], [2, 1, -1, -1, 1, 1, -1], [1, 0, 0, -1, 1, 1, -1],
    [0, 0, 0, 0, 0, 1, -1]]

@[expose] def e7W6Basis : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, -1], [-1, 0, -1, 0, -2, -2, -1], [-2, -1, -2, -2, -2, -2, -1],
    [-2, -1, -1, -1, -2, -2, -1], [-2, 0, -2, -1, -2, -2, -1], [-2, -1, -1, -2, -2, -1, -1],
    [-1, -1, 0, -1, -1, -1, -1]]

@[expose] def e7W6BasisInv : List (List ℤ) :=
  [[0, 1, 1, -1, -1, 0, 0], [-1, 0, -1, -2, 2, 0, 2], [-1, 0, -1, -1, 1, 0, 2],
    [1, 0, 0, 2, -1, 0, -2], [0, -1, 0, 0, 1, -1, 1], [1, 0, 0, 1, -1, 1, -2],
    [-1, 0, 0, 0, 0, 0, 0]]

theorem e7W6_wordMat : wordMat Tag.E7 e7W6Word = toMat Tag.E7.rank e7W6Mat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7W6_pow : (wordMat Tag.E7 e7W6Word) ^ 6 = 1 := by
  rw [e7W6_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7W6_charpoly :
    (wordMat Tag.E7 e7W6Word).charpoly =
      ([6, 6, 2, 2, 1].map fun d => cyclotomic d ℤ).prod := by
  rw [e7W6_wordMat]
  exact charpoly_of_basis e7W6Mat e7W6Basis e7W6BasisInv [6, 6, 2, 2, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

@[expose] def e7PlaneTheta : Fin Tag.E7.rank → ℤ := ![2, 2, 3, 4, 3, 2, 1]

theorem e7PlaneTheta_mem : e7PlaneTheta ∈ rootFinset .E7 := by decide +kernel

theorem e7W6_mulVec_theta : (wordMat Tag.E7 e7W6Word) *ᵥ e7PlaneTheta = e7PlaneTheta := by
  rw [e7W6_wordMat]
  decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube
