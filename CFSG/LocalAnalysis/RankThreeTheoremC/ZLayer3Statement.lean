module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def ZLayerWeakCoreFact3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    CFSG.twoLocalOddRank X ≤ 3 →
    primeComplementCore (G := X) 3 = ⊥ → ∀ (P : Sylow 3 X) (z : X),
      CFSG.Open.pRank 3 (P : Subgroup X) = 3 → orderOf z = 3 → (zpowers z).Normal →
      z ∈ centralizer ((P : Subgroup X) : Set X) → z ∈ rankThreeLayer (⊤ : Subgroup X) →
      IsCyclic (CFSG.pCore 3 X) →
      (∃ D : Subgroup X, (IsIsolatedPlane 3 (P : Subgroup X) D ∨
          IsNonabelianPlane 3 (P : Subgroup X) D) ∧ z ∈ D ∧
        ¬ (P : Subgroup X) ≤ normalizer (D : Set X)) →
      rankThreeLayer (⊤ : Subgroup X) ≤ rankThreeAschCore 2 3 (P : Subgroup X)

end CFSG.LocalAnalysis.RankThreeTheoremC
