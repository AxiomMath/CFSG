module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BRank
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.LocalAnalysis.RankThreeTheoremC (IsMaxTwoInvariantIn)
open CFSG.AGLEmbedding (CatalogSimpleSections)

structure YData (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) : Prop where
  cfg : K62B.Cfg p P x z
  four_le : 4 ≤ Open.pRank p (⊤ : Subgroup Y)
  rank_cent : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2
  perf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤
  plane_card : Nat.card (zpowers x ⊔ zpowers z : Subgroup Y) = p ^ 2
  sc : ∀ y ∈ centralizer ((zpowers x ⊔ zpowers z : Subgroup Y) : Set Y), y ^ p = 1 →
    y ∈ (zpowers x ⊔ zpowers z : Subgroup Y)

@[expose] def KDFieldP5 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Y : Type) [Group Y] [Finite Y], CatalogSimpleSections Y →
    primeComplementCore (G := Y) p = ⊥ →
    ∀ L : Subgroup Y, L.Normal → IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
      ¬ IsLinearOrUnitaryAt p L → centralizer (L : Set Y) = ⊥ →
      4 ≤ Open.pRank p (⊤ : Subgroup Y) → ∀ x : Y, x ∉ L → orderOf x = p →
        3 ≤ Open.pRank p (centralizer ({x} : Set Y)) ∨ ∃ N : Subgroup Y, N.Normal ∧ N.index = p

@[expose] def KD292LinUni : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y), YData p Y P x z →
    ∀ L : Subgroup Y, IsComponentOf L ⊤ → (∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L) →
      IsLinearOrUnitaryAt p (↥L ⧸ center ↥L) →
      ∀ T : Subgroup Y, IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) ⊤ T →
        ∃ Q : Sylow p Y, (Q : Subgroup Y) ≤ normalizer (T : Set Y)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
