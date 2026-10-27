module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

@[expose] def StronglyEmbeddedPSL2KFact : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup K → ∀ (p n : ℕ) [Fact p.Prime], 5 ≤ p → 3 ≤ n →
    ∀ (S : Sylow p K) (L : Subgroup K), (S : Subgroup K) ≤ L →
      Nonempty (L ≃* CFSG.AGLEmbedding.PSL2GF p n) →
      CFSG.Open.GLBCore p 1 (S : Subgroup K) ≠ ⊤ → L = ⊤

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
