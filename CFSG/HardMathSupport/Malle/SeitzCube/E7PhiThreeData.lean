module

public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration Polynomial
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped Matrix

@[expose] def e7W3Word : List (Fin Tag.E7.rank) :=
  [5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 0, 2, 3, 2, 0]

@[expose] def e7W3Mat : List (List ℤ) :=
  [[-1, 1, 1, -1, 0, 0, 1], [0, 1, 0, -1, 0, 0, 2], [-1, 2, 0, -1, 0, 0, 2],
    [0, 3, 0, -2, 0, 0, 3], [0, 2, 0, -1, -1, 1, 2], [0, 1, 0, 0, -1, 0, 2],
    [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7W3Basis : List (List ℤ) :=
  [[1, -1, 0, 1, 0, -1, 0], [0, 0, 1, 1, 0, -1, 0], [0, -1, 0, 2, 0, -1, 0],
    [0, 0, 0, 3, 1, -2, 0], [0, 0, 0, 2, 0, -1, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7W3BasisInv : List (List ℤ) :=
  [[1, 0, -1, 0, 0, 1, 0], [0, 0, -1, 0, 1, 0, 0], [0, 1, 0, 0, -1, 1, 0],
    [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, -2, 1, 0], [0, 0, 0, 0, -1, 2, 0], [0, 0, 0, 0, 0, 0, 1]]

theorem e7W3_wordMat : wordMat Tag.E7 e7W3Word = toMat Tag.E7.rank e7W3Mat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7W3_pow : (wordMat Tag.E7 e7W3Word) ^ 3 = 1 := by
  rw [e7W3_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7W3_charpoly :
    (wordMat Tag.E7 e7W3Word).charpoly = ([3, 3, 3, 1].map fun d => cyclotomic d ℤ).prod := by
  rw [e7W3_wordMat]
  exact charpoly_of_basis e7W3Mat e7W3Basis e7W3BasisInv [3, 3, 3, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

@[expose] def e7Gamma₁ : Fin Tag.E7.rank → ℤ := ![0, 0, 0, 0, 0, 0, 1]

@[expose] def e7Gamma₂ : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 3, 2, 2, 1]

@[expose] def e7Gamma₃ : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 3, 3, 2, 1]

theorem e7Gamma₁_mem : e7Gamma₁ ∈ rootFinset .E7 := by decide +kernel

theorem e7Gamma₂_mem : e7Gamma₂ ∈ rootFinset .E7 := by decide +kernel

theorem e7Gamma₃_mem : e7Gamma₃ ∈ rootFinset .E7 := by decide +kernel

theorem e7W3_mulVec_gamma₁ : (wordMat Tag.E7 e7W3Word) *ᵥ e7Gamma₁ = e7Gamma₂ := by
  rw [e7W3_wordMat]
  decide +kernel

theorem e7W3_mulVec_gamma₂ : (wordMat Tag.E7 e7W3Word) *ᵥ e7Gamma₂ = e7Gamma₃ := by
  rw [e7W3_wordMat]
  decide +kernel

theorem e7W3_mulVec_gamma₃ : (wordMat Tag.E7 e7W3Word) *ᵥ e7Gamma₃ = e7Gamma₁ := by
  rw [e7W3_wordMat]
  decide +kernel

theorem iform_e7Gamma₁₂ : iform e7Gamma₁ e7Gamma₂ = 0 := by decide +kernel

theorem iform_e7Gamma₁₃ : iform e7Gamma₁ e7Gamma₃ = 0 := by decide +kernel

theorem iform_e7Gamma₂₃ : iform e7Gamma₂ e7Gamma₃ = 0 := by decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube
