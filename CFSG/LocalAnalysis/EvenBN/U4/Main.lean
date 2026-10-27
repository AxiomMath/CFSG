module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenBNRankTwoFrontier

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def SimpleStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (L : Subgroup G) (f : ℕ), 2 ≤ f → standardComponentIsStandard L → center L = ⊥ →
    (∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    LieModel L .PSU 4 2 f → False

theorem bnFamily_PSU4_of_simple (h : SimpleStatement) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSU 4 2 f := by
  intro G _ _ _ hnonab _ L hL hcore S hS _ _ ⟨f, hf, hm⟩
  have h2 := ComponentInitial.EvenResidual.isPGroup_two_center hL hcore
  by_contra hodd
  have hZ : center L = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rcases k with _ | k
    · exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
    · exact (hodd (by rw [hk]; exact Nat.even_pow.2 ⟨even_two, by omega⟩)).elim
  let e : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hmL : LieModel L .PSU 4 2 f := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  exact h G hnonab L f hf hL hZ hcore S hS hmL

end CFSG.LocalAnalysis.EvenBN.U4
