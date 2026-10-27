module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSLFourCases
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicThree
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall SporadicFixedSLFourInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section Main


theorem exists_fixed_not_mem_of_sporadic {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {K : Type} [Field K] (hK : Nat.card K = 2) {D : Subgroup S}
    (hfix : ∀ x ∈ D, σ x = x) (hD : Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin 4) K)) :
    ∃ k : S, σ k = k ∧ k ∉ D ∧ ∀ s : S, MulAut.conj s = σ → k * s ∉ D := by
  obtain ⟨eD⟩ := hD
  by_contra hcon
  push Not at hcon
  have := hS
  have hna : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_of_mulEquiv_SL_four eD
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a', b', fun h => hab ?_⟩
    have h' : a' * b' = b' * a' :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']
  have hinj := ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna
  obtain ⟨D', hD', hZ', hcard', hmap', hσD', htop', hidx'⟩ :=
    exists_component_of_not_sporadicFixed hinj hσ hK hfix eD hcon
  have hDcard : Nat.card D = 20160 := card_of_mulEquiv_SL_four hK eD
  have hD'card : Nat.card D' = 20160 := by
    rw [← hDcard, ← hmap', card_map_of_injective (fixedSubgroup σ).subtype_injective]
  have hFout : σ ∉ (MulAut.conj : S →* MulAut S).range → Nat.card (fixedSubgroup σ) = 20160 := by
    intro hout
    rw [← hD'card, htop' hout, card_top]
  have hFin : ∀ u : S, MulAut.conj u = σ → Nat.card (fixedSubgroup σ) = 40320 := by
    intro u hu
    rw [← card_mul_index D', hD'card, hidx' u hu]
  have hdvdS : 20160 ∣ Nat.card S := hDcard ▸ card_subgroup_dvd_card D
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have horder : ∀ u : S, MulAut.conj u = σ → orderOf u = 2 := fun u hu => by
    rw [← orderOf_injective _ hinj u, hu, hσ]
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
  case M22 => exact SporadicRefine.m22_false_of_l34 hS hna e hσ hD' hcard'
  case M23 => exact SporadicRefine.m23_false_of_l34 hS hna e hσ hD' hcard'
  case M24 => exact SporadicRefine.m24_false_of_l34 hS hna e hσ hD' hcard'
  case J2 => exact SporadicRefine.j2_false_of_l34 e hσ hcard'
  case J4 => exact OmegaPilot.false_of_j4_component hS hna e hσ hD'
  case Ru => exact SporadicRefine.ru_false_of_l34 hS hna e hσ hD' hcard'
  case Ly => exact SporadicRefine.ly_false_of_l34 hS hna e hσ hD' hcard'
  case Th => exact LinearPilot.false_of_th_component hS hna e hσ hD'
  case HN => exact LinearPilot.hn_false_of_card_twenty_thousand hS hna e hσ hD' hcard'
  case Co1 =>
    have h := UnitaryPilot.co1_fixed_card_quotient hS hna e hσ hD'
    rw [hcard'] at h
    norm_num at h
  case Co2 => exact UnitaryPilot.co2_false_of_fixed_component hS hna e hσ hD'
  case Co3 =>
    rcases UnitaryPilot.co3_fixed_card_quotient hS hna e hσ hD' with h | h <;>
      rw [hcard'] at h <;> norm_num at h
  case Fi22 =>
    obtain ⟨hin, hout⟩ := UnitaryPilot.fi22_fixed_card_quotient hS hna e hσ hD'
    by_cases h : σ ∈ (MulAut.conj : S →* MulAut S).range
    · have h' := (hin h).1
      rw [hcard'] at h'
      norm_num at h'
    · rcases hout h with h' | h' <;> rw [hcard'] at h' <;> norm_num at h'
  case Fi23 =>
    have h := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hσ hD'
    rw [hcard'] at h
    norm_num at h
  case Fi24Prime =>
    rcases OmegaPilot.fi24_card_quotient_center hS hna e hσ hD' with h | h | h <;>
      rw [hcard'] at h <;> norm_num at h
  case B =>
    rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD' with h | h <;>
      rw [hcard'] at h <;> norm_num at h
  case M =>
    have h := (OmegaPilot.monster_two_part_card_quotient_center
      ComponentClassification.CatLeafProof.monsterInnerInput
      ComponentClassification.CatLeafProof.monsterLocalComponentsInput hS hna e hσ hD').1
    rw [hcard'] at h
    norm_num at h
  case He => exact SporadicRefine.he_false_of_l34 hS hna e hσ hD' hcard' hσD'
  case Suz =>
    obtain ⟨hout, hC⟩ := SporadicRefine.suz_l34_outer_card hS hna e hσ hD' hcard' hσD'
    rw [hFout hout] at hC
    norm_num at hC
  case ONan =>
    by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      rcases hσD' with ⟨-, hsmall⟩ | hfree
      · exact SporadicRefine.on_inner_not_twoSmall e (horder u rfl) hD' hsmall
      · exact LinearPilot.not_mem_range_conj_of_twoFree hna hσ hfree ⟨u, rfl⟩
    · exact on_outer_false_of_SL_four e hσ hin hK hfix eD
  case HS =>
    by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      have h := hFin u rfl
      rw [Nat.card_congr (MulEquiv.subgroupCongr
        (fixedSubgroup_conj_eq_centralizerOf u)).toEquiv] at h
      rcases hs_inner_card_centralizer e (horder u rfl) with h' | h' <;> rw [h'] at h <;>
        norm_num at h
    · obtain ⟨r, hr, ⟨φ⟩⟩ := hs_fixedSubgroup_rows e hσ
      obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
      have hC := (hrows r hr).2.2.2.2.1
      have h := hFout hin
      rw [Nat.card_congr φ.toEquiv, hC] at h
      rcases QuasithinUnique.Id2519.SporHS.hsRows_cases hr with h' | ⟨-, -, h', -⟩ |
        ⟨-, h'⟩ | h' <;> rw [h'] at h <;> norm_num at h
  case McL =>
    by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      exact false_of_mcl_index_two e (horder u rfl) (hidx' u rfl)
    · have hfixS : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
        ext x
        exact Iff.rfl
      let φ := MulEquiv.subgroupCongr hfixS
      have h : Nat.card ((D'.map φ.toMonoidHom) ⧸ center (D'.map φ.toMonoidHom)) = 7920 :=
        ComponentClassification.RestrictedStd.Spor.mcl_outer_comps e σ hσ2 hin _
          (LocalCores.isComponent_map_mulEquiv φ hD')
      have h' : Nat.card ((D'.map φ.toMonoidHom) ⧸ center (D'.map φ.toMonoidHom)) = 20160 := by
        obtain ⟨ψ⟩ := nonempty_quotient_center_map_equiv φ D'
        rw [← Nat.card_congr ψ.toEquiv, hcard']
      rw [h] at h'
      norm_num at h'

theorem sporadicFixedSLFourInput_of_simple
    (hsimple : ∀ (S : Type) [Group S] [Finite S], NativeSporadic.SporadicRep S →
      IsSimpleGroup S) : SporadicFixedSLFourInput := by
  intro S _ _ hsp σ hσ K _ hK D hfix hD
  exact exists_fixed_not_mem_of_sporadic (hsimple S hsp) hsp hσ hK hfix hD

end Main

end CFSG.SeitzReduction.SporadicRefine
