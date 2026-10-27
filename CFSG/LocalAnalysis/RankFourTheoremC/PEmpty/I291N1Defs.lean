module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.AGLEmbedding (CatalogSimpleSections)

@[expose] def KDMultP5 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ center K) → center K ≠ ⊥ → IsPGroup p (center K) →
      IsLinearOrUnitaryAt p (K ⧸ center K)

@[expose] def KDR3Exclusion : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Y : Type) [Group Y] [Finite Y], CatalogSimpleSections Y →
    primeComplementCore (G := Y) p = ⊥ →
    ∀ S : Subgroup Y, S.Normal → IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      centralizer (S : Set Y) = ⊥ → Open.pRank 3 S ≤ 1 → 4 ≤ Open.pRank p (⊤ : Subgroup Y) →
      (∃ x : Y, orderOf x = p ∧ Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) →
        ∃ N : Subgroup Y, N.Normal ∧ N.index = p

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
