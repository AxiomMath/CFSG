module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.Open CFSG.AGLEmbedding

@[expose] def KEStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ T : Sylow p K,
      IsMulCommutative (T : Subgroup K) → 3 ≤ Open.pRank p (T : Subgroup K) →
      GLBCore p 1 (T : Subgroup K) ≠ ⊤ → ∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ≃* PSL2GF p n)

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
