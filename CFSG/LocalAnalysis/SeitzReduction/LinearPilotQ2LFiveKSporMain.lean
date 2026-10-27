module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKSpor
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicSix
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatSporadic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def LFiveSmallOddLieRankInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), IsComponent D → LieModel (D ⧸ center D) .PSL 3 2 1 →
      (F4Pilot.FixedCentralizerTwoFree τ D ∨
        (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D)) →
      ∀ E : Subgroup S, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 8

section Main


theorem eq_J2_of_lFiveSmallKind_sporadic {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {τ : MulAut S}
    (hτ : orderOf τ = 2) {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1)
    (h2 : F4Pilot.FixedCentralizerTwoFree τ D ∨
      (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D)) :
    Nonempty (S ≃* NativeSporadic.J2) := by
  have hcard : Nat.card (D ⧸ center D) = 168 := card_of_lieModel_PSL_three_two hDm
  have hsmall := fixedCentralizerTwoSmall_of_lFive_hyp h2
  have hdvdS : 168 ∣ Nat.card S := by
    rw [← hcard]
    exact (card_quotient_dvd_card _).trans ((card_subgroup_dvd_card D).trans
      (card_subgroup_dvd_card (fixedSubgroup τ)))
  obtain ⟨s, ⟨e⟩⟩ := hsp
  cases s
  case M11 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M11] at hdvdS
    norm_num at hdvdS
  case M12 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12] at hdvdS
    norm_num at hdvdS
  case J3 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.J3.card_J3] at hdvdS
    norm_num at hdvdS
  case J2 => exact ⟨e⟩
  case J1 => exact (j1_false_of_lThree hS hna e hτ D hcard).elim
  case M22 => exact (m22_false_of_lThree hS hna e hτ hD hcard).elim
  case M23 => exact (m23_false_of_lThree hS hna e hτ hD hcard).elim
  case M24 => exact (m24_false_of_lThree hS hna e hτ hD hcard).elim
  case Ru => exact (ru_false_of_lThree hS hna e hτ hD hcard).elim
  case Ly => exact (ly_false_of_lThree hS hna e hτ hD hcard).elim
  case J4 => exact (OmegaPilot.false_of_j4_component hS hna e hτ hD).elim
  case Th => exact (false_of_th_component hS hna e hτ hD).elim
  case HN => exact (hn_false_of_lThree hS hna e hτ hD hcard).elim
  case Co1 =>
    have h := UnitaryPilot.co1_fixed_card_quotient hS hna e hτ hD
    rw [hcard] at h
    norm_num at h
  case Co2 => exact (UnitaryPilot.co2_false_of_fixed_component hS hna e hτ hD).elim
  case Co3 =>
    rcases UnitaryPilot.co3_fixed_card_quotient hS hna e hτ hD with h | h <;>
      rw [hcard] at h <;> norm_num at h
  case Fi22 =>
    obtain ⟨hin, hout⟩ := UnitaryPilot.fi22_fixed_card_quotient hS hna e hτ hD
    by_cases h : τ ∈ (MulAut.conj : S →* MulAut S).range
    · have h' := (hin h).1
      rw [hcard] at h'
      norm_num at h'
    · rcases hout h with h' | h' <;> rw [hcard] at h' <;> norm_num at h'
  case Fi23 =>
    have h := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hτ hD
    rw [hcard] at h
    norm_num at h
  case Fi24Prime =>
    rcases OmegaPilot.fi24_card_quotient_center hS hna e hτ hD with h | h | h <;>
      rw [hcard] at h <;> norm_num at h
  case B =>
    rcases OmegaPilot.baby_card_quotient_center hS hna e hτ hD with h | h <;>
      rw [hcard] at h <;> norm_num at h
  case M =>
    have h := (OmegaPilot.monster_two_part_card_quotient_center
      ComponentClassification.CatLeafProof.monsterInnerInput
      ComponentClassification.CatLeafProof.monsterLocalComponentsInput hS hna e hτ hD).1
    rw [hcard] at h
    norm_num at h
  case He => exact (he_false_of_lThree hS hna e hτ hD hcard h2).elim
  case Suz => exact (suz_false_of_lThree hS hna e hτ hD hDm h2).elim
  case ONan => exact (on_false_of_lThree hS hna e hτ hD hDm h2).elim
  case HS => exact (hs_false_of_lThree e hτ hD hDm hsmall).elim
  case McL => exact (mcl_false_of_lThree hS hna e hτ hD hcard).elim

theorem lFiveSmallKindRankInput_of_oddLie (hodd : LFiveSmallOddLieRankInput) :
    LFiveSmallKindRankInput := by
  intro S _ _ hq hZ τ hτ D hD hDm h2 hsm
  obtain ⟨-, hsq, ⟨a₀, b₀, hab₀⟩⟩ := hq
  have hS : IsSimpleGroup S := by
    have := hsq
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hna : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b₀
    exact ⟨a, b, fun h => hab₀ (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  set ι : S ⧸ center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot with hι
  obtain ⟨-, h4 | ⟨-, hodd'⟩ | ⟨-, hsp⟩⟩ := hsm
  · exact absurd h4.1 (by norm_num)
  · left
    obtain ⟨t, n, p, f, hp, hp2, hadm, hL⟩ := hodd'
    exact hodd S hS hna ⟨t, n, p, f, hp, hp2, hadm,
      LieType.CurtisTits.lieModel_of_mulEquiv ι hL⟩ τ hτ D hD hDm h2
  · right
    obtain ⟨s, ⟨e⟩⟩ := hsp
    exact eq_J2_of_lFiveSmallKind_sporadic hS hna ⟨s, ⟨ι.symm.trans e⟩⟩ hτ hD hDm h2

end Main

end CFSG.SeitzReduction.LinearPilot
