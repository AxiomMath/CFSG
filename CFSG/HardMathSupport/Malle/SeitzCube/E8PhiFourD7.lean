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

@[expose] def e8D7FourWord : List (Fin Tag.E8.rank) :=
  [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 3, 2, 1]

@[expose] def e8D7FourMat : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0], [1, -1, 0, 1, -1, 1, -1, 1], [2, 0, -1, 1, -1, 1, -1, 1], [3, -1, -1,
  1, -1, 2, -2, 2], [2, 0, 0, 0, -1, 2, -2, 2], [2, 0, 0, 0, -1, 1, -1, 2], [1, 0, 0, 0, 0, 0, -1,
  2], [1, 0, 0, 0, 0, 0, -1, 1]]

@[expose] def e8D7FourBasis : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, -2, 1], [1, -3, 0, -1, 0, -1, 1, 0], [1, -3, 0, -1, 0, -1, 0, 0], [-1, -6, 0,
  -2, 0, -1, 0, 0], [-1, -3, 0, -2, 1, -1, 0, 0], [-1, -2, -1, -2, 1, -2, 0, 0], [0, -2, -1, -1, 0,
  -2, 0, 0], [-1, -1, -1, 0, -1, -1, 0, 0]]

@[expose] def e8D7FourBasisInv : List (List ℤ) :=
  [[0, 0, 1, 0, -1, 1, -1, 0], [0, 0, 1, -1, 1, 0, -1, 1], [0, 0, 0, -2, 5, -4, 2, 1], [0, 0, -4, 2,
  -1, -2, 5, -3], [0, 0, -3, 2, -2, 0, 3, -3], [0, 0, 1, 1, -3, 3, -3, 0], [0, 1, -1, 0, 0, 0, 0,
  0], [1, 2, -2, 0, 0, 0, 0, 0]]

theorem e8D7Four_wordMat :
    wordMat Tag.E8 e8D7FourWord = toMat Tag.E8.rank e8D7FourMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8D7Four_pow : (wordMat Tag.E8 e8D7FourWord) ^ 4 = 1 := by
  rw [e8D7Four_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8D7Four_charpoly :
    (wordMat Tag.E8 e8D7FourWord).charpoly =
      ([4, 4, 4, 1, 2].map fun d => cyclotomic d ℤ).prod := by
  rw [e8D7Four_wordMat]
  exact charpoly_of_basis e8D7FourMat e8D7FourBasis e8D7FourBasisInv [4, 4, 4, 1, 2]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

@[expose] def e8D7Gamma : Fin Tag.E8.rank → ℤ := ![2, 2, 4, 5, 4, 3, 2, 1]

@[expose] def e8D7GammaW : Fin Tag.E8.rank → ℤ := ![2, 3, 3, 5, 4, 3, 2, 1]

theorem e8D7Gamma_mem : e8D7Gamma ∈ rootFinset .E8 := by decide +kernel

theorem e8D7GammaW_mem : e8D7GammaW ∈ rootFinset .E8 := by decide +kernel

theorem e8D7Four_mulVec_gamma :
    (wordMat Tag.E8 e8D7FourWord) *ᵥ e8D7Gamma = e8D7GammaW := by
  rw [e8D7Four_wordMat]
  decide +kernel

theorem e8D7Four_mulVec_gammaW :
    (wordMat Tag.E8 e8D7FourWord) *ᵥ e8D7GammaW = e8D7Gamma := by
  rw [e8D7Four_wordMat]
  decide +kernel

theorem e8D7Gamma_ne : e8D7Gamma ≠ e8D7GammaW := by decide +kernel

theorem e8D7Gamma_orth : iform e8D7Gamma e8D7GammaW = 0 := by decide +kernel

theorem e8D7Gamma_height : 0 < height e8D7Gamma := by decide +kernel

theorem e8D7GammaW_height : 0 < height e8D7GammaW := by decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube
