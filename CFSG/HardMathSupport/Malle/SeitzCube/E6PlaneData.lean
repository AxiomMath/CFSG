module

public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration Polynomial
open scoped Matrix

@[expose] def e6W3Word : List (Fin Tag.E6.rank) := [4, 5, 0, 2]

@[expose] def e6W3Mat : List (List ℤ) := [[0, 0, -1, 1, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, -1, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 1, -1]]

@[expose] def e6W3Basis : List (List ℤ) := [[0, 1, 0, -1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, 1, 1, -1, 0, 0], [0, 0, 0, 0, 0, 1], [1, 1, -1, 0, 0, 0], [-1, 2, 0, -1, 0, 0]]

@[expose] def e6W3BasisInv : List (List ℤ) := [[0, 0, 1, 0, 1, -1], [-1, 0, 1, 0, 1, 0], [-1, 0, 2, 0, 1, -1], [-2, 0, 1, 0, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0]]

theorem e6W3_wordMat : wordMat Tag.E6 e6W3Word = toMat Tag.E6.rank e6W3Mat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6W3_pow : (wordMat Tag.E6 e6W3Word) ^ 3 = 1 := by
  rw [e6W3_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6W3_charpoly :
    (wordMat Tag.E6 e6W3Word).charpoly =
      ([3, 3, 1, 1].map fun d => cyclotomic d ℤ).prod := by
  rw [e6W3_wordMat]
  exact charpoly_of_basis e6W3Mat e6W3Basis e6W3BasisInv [3, 3, 1, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

@[expose] def e6PlaneTheta : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

theorem e6PlaneTheta_mem : e6PlaneTheta ∈ rootFinset .E6 := by decide +kernel

theorem e6W3_mulVec_theta : (wordMat Tag.E6 e6W3Word) *ᵥ e6PlaneTheta = e6PlaneTheta := by
  rw [e6W3_wordMat]
  decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube
