module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.Setup
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenBNRankTwoFrontier

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def G2CenterlessExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L → center L = ⊥ →
    (∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    (∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G)))) →
    ∀ f : ℕ, 2 ≤ f → LieModel L .G2 0 2 f → False

theorem bnFamily_G2_of_exclusion (h : G2CenterlessExclusion) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .G2 0 2 f := by
  intro G _ _ _ hnonab hK L hL hcore S hS _ _ ⟨f, hf, hm⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := ComponentInitial.EvenResidual.isPGroup_two_center hL hcore
  by_contra hodd
  have hZ : center L = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rcases k with _ | k
    · exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
    · exact (hodd (by rw [hk]; exact Nat.even_pow.2 ⟨even_two, by omega⟩)).elim
  let e : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hmL : LieModel L .G2 0 2 f := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  exact h G hnonab hK L hL hZ hcore (LinearThree.isCyclic_of_isCyclic_sylow S hS) f hf hmL

end CFSG.LocalAnalysis.EvenBN.G2
