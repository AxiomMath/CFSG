module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenBNRankTwoFrontier

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def TwoF4CenterlessExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    center L = ⊥ → ∀ f : ℕ, Odd f → 3 ≤ f → LieModel L .twistedF4 0 2 f → False

theorem bnFamily_twistedF4_of_exclusion (h : TwoF4CenterlessExclusion) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ LieModel X .twistedF4 0 2 f := by
  intro G _ _ _ hnonab hK L hL hcore S hS _ _ ⟨f, hodd, hf, hm⟩
  have h2 := ComponentInitial.EvenResidual.isPGroup_two_center hL hcore
  by_contra hev
  have hZ : center L = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rcases k with _ | k
    · exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
    · exact (hev (by rw [hk]; exact Nat.even_pow.2 ⟨even_two, by omega⟩)).elim
  let e : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hmL : LieModel L .twistedF4 0 2 f := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  exact h G hnonab hK L hL hcore S hS hZ f hodd hf hmL

end CFSG.LocalAnalysis.EvenBN.TwoF4
