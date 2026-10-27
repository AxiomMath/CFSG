module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineLFourRankCases

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section Main


theorem sporadic_alt_eight_component {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {τ : MulAut S}
    (hτ : orderOf τ = 2) {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (eD : D ≃* alternatingGroup (Fin 8))
    (h2 : (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D) ∨
      FixedCentralizerTwoFree τ D) :
    τ ∉ (MulAut.conj : S →* MulAut S).range ∧ Nonempty (S ≃* NativeSporadic.HS) := by
  have hZ : center D = ⊥ := CFSG.OddStandard.AltStdSec.center_eq_bot_of_alt (by norm_num) eD
  have eQ : (D ⧸ center D) ≃* alternatingGroup (Fin 8) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eD
  have hDm : LieModel (D ⧸ center D) .PSL 4 2 1 :=
    (ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2 ⟨eQ⟩
  have hcard' : Nat.card (D ⧸ center D) = 20160 := by
    rw [Nat.card_congr eQ.toEquiv]
    exact card_alternatingGroup_eight
  have hDcard : Nat.card D = 20160 := by
    rw [Nat.card_congr eD.toEquiv]
    exact card_alternatingGroup_eight
  have hdvdS : 20160 ∣ Nat.card S := by
    rw [← hDcard]
    exact (card_subgroup_dvd_card D).trans (card_subgroup_dvd_card (fixedSubgroup τ))
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
  case He => exact (SporadicRefine.he_false_of_l34 hS hna e hτ hD hcard' h2).elim
  case Suz =>
    obtain ⟨hout, hC⟩ := SporadicRefine.suz_l34_outer_card hS hna e hτ hD hcard' h2
    exact (suz_not_lieModel_psl_four_two e hC hD (h2.resolve_left fun h => hout h.1) hDm).elim
  case ONan =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      rcases h2 with ⟨-, hsmall⟩ | hfree
      · exact (SporadicRefine.on_inner_not_twoSmall e
          (orderOf_eq_two_of_conj_of_simple hS hna hτ) hD hsmall).elim
      · exact (LinearPilot.not_mem_range_conj_of_twoFree hna hτ hfree ⟨u, rfl⟩).elim
    · exact (on_outer_not_lieModel_psl_four_two e hτ hin
        (h2.resolve_left fun h => hin h.1) hDm).elim
  case HS =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · exfalso
      obtain ⟨u, rfl⟩ := hin
      have hu := orderOf_eq_two_of_conj_of_simple hS hna hτ
      have h1 : Nat.card D ∣ Nat.card (fixedSubgroup (MulAut.conj u)) :=
        card_subgroup_dvd_card D
      rw [Nat.card_congr (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf u)).toEquiv,
        hDcard] at h1
      rcases hs_inner_card_centralizer e hu with h' | h' <;> rw [h'] at h1 <;> norm_num at h1
    · exact ⟨hin, ⟨e⟩⟩
  case McL =>
    exfalso
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      have hu := orderOf_eq_two_of_conj_of_simple hS hna hτ
      obtain ⟨-, hcen, ⟨φ⟩⟩ :=
        Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate ⟨e⟩ hu
      set c : centralizer ({u} : Set S) :=
        ⟨u, Sporadic.Recognition.McLCentralizer.self_mem_centralizer u⟩ with hc
      have hz : Nat.card (zpowers c) = 2 := by
        rw [Nat.card_zpowers, hc, Subgroup.orderOf_mk, hu]
      have hC : Nat.card (centralizer ({u} : Set S)) = 40320 := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers c), Nat.card_congr φ.toEquiv,
          card_alternatingGroup_eight, hz]
      have hF : Nat.card (fixedSubgroup (MulAut.conj u)) = 40320 := by
        rw [Nat.card_congr (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf u)).toEquiv,
          hC]
      have hidx : D.index = 2 := by
        have h1 := card_mul_index D
        rw [hDcard, hF] at h1
        omega
      exact false_of_mcl_index_two e hu hidx
    · have hσ2 : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
      have hfixS : fixedSubgroup τ = Sporadic.Schreier.fixSub τ := by
        ext x
        exact Iff.rfl
      let φ := MulEquiv.subgroupCongr hfixS
      have h : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = 7920 :=
        ComponentClassification.RestrictedStd.Spor.mcl_outer_comps e τ hσ2 hin _
          (LocalCores.isComponent_map_mulEquiv φ hD)
      have h' : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = 20160 := by
        obtain ⟨ψ⟩ := nonempty_quotient_center_map_equiv φ D
        rw [← Nat.card_congr ψ.toEquiv, hcard']
      rw [h] at h'
      norm_num at h'

end Main

end CFSG.SeitzReduction.SporadicRefine
