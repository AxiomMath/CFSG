module

public import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

@[expose] def sectionExcludedNames3 : Finset TauCeti.SporadicName :=
  {.Fi22, .Fi23, .Fi24Prime, .B, .M}

@[expose] def NotSecExcl3 (K : Type) [Group K] : Prop :=
  ∀ s ∈ sectionExcludedNames3, ¬ Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group)

theorem notSecExcl3_of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L)
    (h : NotSecExcl3 L) : NotSecExcl3 K :=
  fun s hs ⟨f⟩ => h s hs ⟨e.symm.trans f⟩

@[expose] def KFactBetaRank2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K, (T : Subgroup K) ≠ ⊥ →
      Open.pRank p (T : Subgroup K) ≤ 2 →
      (IsCyclic (T : Subgroup K) ∨ GLBCore p 1 (T : Subgroup K) ≠ ⊤) →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

@[expose] def NoExcludedSection3 (G : Type) [Group G] : Prop :=
  ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal] (K : Subgroup (H ⧸ N)),
    Open.IsQuasisimple K → NotSecExcl3 (K ⧸ Subgroup.center K)

structure KFactsA3 (G : Type) [Group G] : Prop where
  beta : KFactBetaRank2
  noExcl : NoExcludedSection3 G

end CFSG.LocalAnalysis.RankThreeTheoremC
