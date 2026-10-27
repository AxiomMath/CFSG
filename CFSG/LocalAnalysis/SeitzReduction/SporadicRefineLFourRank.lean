module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineLFourRankCases
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWSmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section Main


theorem sixSmallKindRankInput : LinearPilot.SixSmallKindRankInput := by
  intro S _ _ hq hZ hsp τ hτ D hD hDm h2 E hE
  obtain ⟨-, hsq, ⟨a₀, b₀, hab₀⟩⟩ := hq
  have hS : IsSimpleGroup S := by
    have := hsq
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hna : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b₀
    exact ⟨a, b, fun h => hab₀ (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hcard' : Nat.card (D ⧸ center D) = 20160 := by
    rw [LinearPilot.card_of_lieModel_PSL_two hDm]
    decide
  have hσD' : (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D) ∨
      FixedCentralizerTwoFree τ D := h2.symm
  have hdvdS : 20160 ∣ Nat.card S := by
    rw [← hcard']
    exact ((Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)) ▸
      Dvd.intro _ rfl).trans ((card_subgroup_dvd_card D).trans
        (card_subgroup_dvd_card (fixedSubgroup τ)))
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [h32]
  obtain ⟨s, ⟨e⟩⟩ := hsp
  cases s
  case M11 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M11] at hdvdS
    norm_num at hdvdS
  case M12 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12] at hdvdS
    norm_num at hdvdS
  case J1 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.J1.card_J1] at hdvdS
    norm_num at hdvdS
  case J3 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.J3.card_J3] at hdvdS
    norm_num at hdvdS
  case M22 => exact (SporadicRefine.m22_false_of_l34 hS hna e hτ hD hcard').elim
  case M23 => exact (SporadicRefine.m23_false_of_l34 hS hna e hτ hD hcard').elim
  case M24 => exact (SporadicRefine.m24_false_of_l34 hS hna e hτ hD hcard').elim
  case J2 => exact (SporadicRefine.j2_false_of_l34 e hτ hcard').elim
  case J4 => exact (OmegaPilot.false_of_j4_component hS hna e hτ hD).elim
  case Ru => exact (SporadicRefine.ru_false_of_l34 hS hna e hτ hD hcard').elim
  case Ly => exact (SporadicRefine.ly_false_of_l34 hS hna e hτ hD hcard').elim
  case Th => exact (LinearPilot.false_of_th_component hS hna e hτ hD).elim
  case HN => exact (LinearPilot.hn_false_of_card_twenty_thousand hS hna e hτ hD hcard').elim
  case Co1 =>
    have h := UnitaryPilot.co1_fixed_card_quotient hS hna e hτ hD
    rw [hcard'] at h
    norm_num at h
  case Co2 => exact (UnitaryPilot.co2_false_of_fixed_component hS hna e hτ hD).elim
  case Co3 =>
    rcases UnitaryPilot.co3_fixed_card_quotient hS hna e hτ hD with h | h <;>
      rw [hcard'] at h <;> norm_num at h
  case Fi22 =>
    obtain ⟨hin, hout⟩ := UnitaryPilot.fi22_fixed_card_quotient hS hna e hτ hD
    by_cases h : τ ∈ (MulAut.conj : S →* MulAut S).range
    · have h' := (hin h).1
      rw [hcard'] at h'
      norm_num at h'
    · rcases hout h with h' | h' <;> rw [hcard'] at h' <;> norm_num at h'
  case Fi23 =>
    have h := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hτ hD
    rw [hcard'] at h
    norm_num at h
  case Fi24Prime =>
    rcases OmegaPilot.fi24_card_quotient_center hS hna e hτ hD with h | h | h <;>
      rw [hcard'] at h <;> norm_num at h
  case B =>
    rcases OmegaPilot.baby_card_quotient_center hS hna e hτ hD with h | h <;>
      rw [hcard'] at h <;> norm_num at h
  case M =>
    have h := (OmegaPilot.monster_two_part_card_quotient_center
      ComponentClassification.CatLeafProof.monsterInnerInput
      ComponentClassification.CatLeafProof.monsterLocalComponentsInput hS hna e hτ hD).1
    rw [hcard'] at h
    norm_num at h
  case He => exact (SporadicRefine.he_false_of_l34 hS hna e hτ hD hcard' hσD').elim
  case Suz =>
    obtain ⟨hout, hC⟩ := SporadicRefine.suz_l34_outer_card hS hna e hτ hD hcard' hσD'
    exact (suz_not_lieModel_psl_four_two e hC hD
      (hσD'.resolve_left fun h => hout h.1) hDm).elim
  case ONan =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      rcases hσD' with ⟨-, hsmall⟩ | hfree
      · exact (SporadicRefine.on_inner_not_twoSmall e
          (orderOf_eq_two_of_conj_of_simple hS hna hτ) hD hsmall).elim
      · exact (LinearPilot.not_mem_range_conj_of_twoFree hna hτ hfree ⟨u, rfl⟩).elim
    · exact (on_outer_not_lieModel_psl_four_two e hτ hin
        (hσD'.resolve_left fun h => hin h.1) hDm).elim
  case HS =>
    have h := hs_card_lt_of_mul_self e hE
    omega
  case McL => exact mcl_card_le_of_mul_self e hE

end Main

end CFSG.SeitzReduction.SporadicRefine
