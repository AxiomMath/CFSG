module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactOneLieSylowCount : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      Nat.card (Sylow p K) = Nat.card (T : Subgroup K) + 1

end CFSG.AGLEmbedding
