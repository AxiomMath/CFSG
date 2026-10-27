module

public import CFSG.LocalAnalysis.EvenBN.U5.Setting
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenBNRankTwoFrontier

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.Blueprint

theorem bnFamily_PSU5_of_exclusion (h : CenterlessExclusion) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSU 5 2 f := by
  intro G _ _ _ hnonab hK L hL hcore S hS _ _ ⟨f, hf, hm⟩
  have h2 := ComponentInitial.EvenResidual.isPGroup_two_center hL hcore
  by_contra hodd
  have hZ : center L = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rcases k with _ | k
    · exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
    · exact (hodd (by rw [hk]; exact Nat.even_pow.2 ⟨even_two, by omega⟩)).elim
  let e : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hmL : LieModel L .PSU 5 2 f := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  exact h G L f ⟨⟨inferInstance, hnonab, hK, hL, hcore, ⟨S, hS⟩⟩, hf, hZ, hmL⟩

end CFSG.LocalAnalysis.EvenBN.U5
