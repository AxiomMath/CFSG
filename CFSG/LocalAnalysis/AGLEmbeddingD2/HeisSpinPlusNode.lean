module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinPlus

public section

namespace CFSG.AGLEmbeddingD2.HeisSpinPlus

open CFSG.LieType.Universal.Spin CFSG.AGLEmbeddingD2.SquareSpinPlus

variable {n : ℕ}

theorem nodeX_of_lt {k : Fin n} (h : k.val + 1 < n) : nodeX k = Sum.inl k := by
  simp [nodeX, rootIdxD_of_lt n h]

theorem nodeY_of_lt {k : Fin n} (h : k.val + 1 < n) : nodeY k = Sum.inr ⟨k.val + 1, h⟩ := by
  simp [nodeY, rootIdxD'_of_lt n h, rootSignD_of_lt n h]

theorem nodeX_of_last {k : Fin n} (h : k.val + 1 = n) (hn : 2 ≤ n) :
    nodeX k = Sum.inl ⟨n - 2, by omega⟩ := by
  have h1 : ¬ k.val + 1 < n := by omega
  simp [nodeX, rootIdxD, h1]

theorem nodeY_of_last {k : Fin n} (h : k.val + 1 = n) (hn : 2 ≤ n) :
    nodeY k = Sum.inl ⟨n - 1, by omega⟩ := by
  simp [nodeY, rootIdxD', rootSignD, h]

end CFSG.AGLEmbeddingD2.HeisSpinPlus
