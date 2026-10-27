module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.AGLEmbedding.UnitaryLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def levi (N B : Matrix (Fin r) (Fin r) K) : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  fromBlocks N 0 0 (fromBlocks 1 0 0 B)

theorem levi_mul (N B N' B' : Matrix (Fin r) (Fin r) K) :
    (levi N B : Matrix (HypIndex r ε) (HypIndex r ε) K) * levi N' B' = levi (N * N') (B * B') := by
  simp [levi, fromBlocks_multiply]

theorem levi_isometry (h : UnitaryFieldData p f K) (N B : Matrix (Fin r) (Fin r) K)
    (hNB : (N.map h.bar)ᵀ * B = 1) :
    ((levi N B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      levi N B = hypGram r ε K := by
  have hBN : (B.map h.bar)ᵀ * N = 1 := by
    have hbb : ∀ M : Matrix (Fin r) (Fin r) K, (M.map h.bar).map h.bar = M := fun M => by
      ext; simp [h.bar_bar]
    have := congrArg (fun X => (X.map h.bar)ᵀ) hNB
    simp only [Matrix.map_mul, transpose_mul, ← transpose_map, transpose_transpose, hbb,
      transpose_one] at this
    simpa [transpose_map] using this
  simp only [levi, hypGram, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply]
  simp [fromCols_mul_fromBlocks, fromBlocks_mul_fromRows, fromRows_mul, fromBlocks_multiply, hNB, hBN]

end CFSG.AGLEmbedding.UnitaryLevi
