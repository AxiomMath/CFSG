module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineCo3
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSuz
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineON
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.Sporadic.ThSchreier.ThSchreierCase

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (isComponent_map_mulEquiv exists_conj_or_not_mem_range)
open CFSG.Sporadic.Schreier (fixSub)

theorem center_eq_bot_and_card_quotient_of_lieModel_PSp {X : Type} [Group X] {D : Subgroup X}
    (hD : IsComponent D) {n f : ℕ} (hDm : LieModel D .PSp n 2 f) :
    center D = ⊥ ∧ Nat.card (D ⧸ center D) = Nat.card D := by
  have hs := F4Pilot.isSimpleGroup_of_lieModel_PSp hDm
  have hZ := F4Pilot.center_eq_bot_of_isQuasisimple hD.1 hs
  exact ⟨hZ, Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv⟩

theorem card_quotient_center_sp6_two {X : Type} [Group X] {D : Subgroup X} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1) : Nat.card (D ⧸ center D) = 1451520 := by
  rw [(center_eq_bot_and_card_quotient_of_lieModel_PSp hD hDm).2,
    F4Pilot.card_of_lieModel_PSp_three_two hDm]
  norm_num

theorem card_quotient_center_sp6_four {X : Type} [Group X] {D : Subgroup X} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 2) : Nat.card (D ⧸ center D) = 4106059776000 := by
  rw [(center_eq_bot_and_card_quotient_of_lieModel_PSp hD hDm).2,
    F4Pilot.card_of_lieModel_PSp_three_two hDm]
  norm_num

section Baby

theorem sp6_false_of_baby {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .B) {σ : MulAut S}
    (hσ : orderOf σ = 2) {f : ℕ} (hf : f = 1 ∨ f = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel D .PSp 3 2 f) : False := by
  have h := OmegaPilot.baby_card_quotient_center hS hna e hσ hD
  rcases hf with rfl | rfl
  · rw [card_quotient_center_sp6_two hD hDm] at h
    omega
  · rw [card_quotient_center_sp6_four hD hDm] at h
    omega

end Baby

section Th

theorem false_of_th_component {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Th) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) : False := by
  have hinn : σ ∈ ComponentClassification.OuterAutomorphisms.inner S := by
    rw [(Sporadic.ThSchreier.ctuc_Th_full_automorphism_group.2 S ⟨e⟩).1]
    exact Subgroup.mem_top σ
  obtain ⟨u, rfl⟩ := hinn
  have hu := OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj u)
  have hB := isComponent_map_mulEquiv φ hD
  have hchar :=
    ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two).2.2 S
      ⟨e⟩).1 u hu
  exact ComponentClassification.RestrictedStd.Spor.compsSatisfy_of_charP hchar.1
    (fun (_ : Type) [Group _] => False) _ hB

end Th

section Fi23

theorem sp6_false_of_fi23 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1) : False := by
  have h := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hσ hD
  rw [card_quotient_center_sp6_two hD hDm] at h
  omega

end Fi23

section Fi24

theorem sp6_false_of_fi24 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi24Prime) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1) : False := by
  have h := OmegaPilot.fi24_card_quotient_center hS hna e hσ hD
  rw [card_quotient_center_sp6_two hD hDm] at h
  omega

end Fi24

section Co1

theorem sp6_false_of_co1 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co1) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1) : False := by
  obtain ⟨u, rfl⟩ :=
    ComponentClassification.BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_Co1 σ
  obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
  have h := (ComponentClassification.RestrictedStd.Spor.co1LocalComponentsInput_holds S e u
    (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB).1
  rw [hcard, card_quotient_center_sp6_two hD hDm] at h
  omega

end Co1

section Co2

theorem false_of_co2_component {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co2) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) : False := by
  obtain ⟨u, rfl⟩ :=
    ComponentClassification.BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_Co2 σ
  obtain ⟨B, hB, -⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
  exact Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e u
    (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB

end Co2

section HN

theorem sp6_false_of_hn {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .HN) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1) : False := by
  rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
    have h := ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds S e u
      (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB
    rw [hcard, card_quotient_center_sp6_two hD hDm] at h
    omega
  · obtain ⟨φ⟩ := ComponentClassification.RestrictedStd.Spor.hnOuterFixInput S e σ hσ hout
    have hfix : Nat.card (fixedSubgroup σ) = 3628800 := by
      rw [Nat.card_congr (MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub σ)).toEquiv,
        Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have hDc : Nat.card D = 1451520 := by
      rw [F4Pilot.card_of_lieModel_PSp_three_two hDm]
      norm_num
    have hdvd := Subgroup.card_subgroup_dvd_card D
    rw [hDc, hfix] at hdvd
    norm_num at hdvd

end HN

section Suz

theorem sp6_false_of_suz {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Suz) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1) : False := by
  rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
    have h := Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e u
      (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB
    rw [hcard, card_quotient_center_sp6_two hD hDm] at h
    omega
  · apply suz_outer_not_dvd_card_fixedSubgroup e hσ hout
    have hDc : Nat.card D = 1451520 := by
      rw [F4Pilot.card_of_lieModel_PSp_three_two hDm]
      norm_num
    exact hDc ▸ Subgroup.card_subgroup_dvd_card D

end Suz

section ON

theorem sp6_false_of_on {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .ONan) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1) : False := by
  rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
    have h := Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
      ⟨e⟩ u (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB
    rw [hcard, card_quotient_center_sp6_two hD hDm] at h
    omega
  · exact on_outer_false_of_lieModel e hσ hout hDm

end ON

section Fi22

theorem sp6_false_of_fi22 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi22) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1)
    (hcase : σ ∈ (MulAut.conj : S →* MulAut S).range ∨ F4Pilot.FixedCentralizerTwoFree σ D) :
    False := by
  rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
    have h := Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order
      e u (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB
    rw [hcard, card_quotient_center_sp6_two hD hDm] at h
    omega
  · exact fi22_outer_not_twoFree_of_lieModel e hσ hout hD hDm (hcase.resolve_left hout)

end Fi22

section Co3

theorem sp6_false_of_co3 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co3) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 1) : False := by
  obtain ⟨u, rfl⟩ := RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.2.2.2.2 S ⟨e⟩ σ
  have hu := OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj u)
  have hB := isComponent_map_mulEquiv φ hD
  obtain ⟨hc1, hc2⟩ :=
    card_center_and_quotient_of_mulEquiv (D.equivMapOfInjective φ.toMonoidHom φ.injective)
  obtain ⟨hZ, -⟩ := center_eq_bot_and_card_quotient_of_lieModel_PSp hD hDm
  have hq := card_quotient_center_sp6_two hD hDm
  rcases co3_involution_component_card ⟨e⟩ hu hB with ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [← hc1, hZ, Subgroup.card_bot] at h1
    omega
  · rw [← hc2, hq] at h2
    omega

end Co3

section Residual

theorem catSp6SporadicResidual_holds : F4Pilot.CatSp6SporadicResidual := by
  intro S _ _ hS hna s ⟨e⟩ σ hσ f D hD hDm hcase hr
  rcases hr with ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sp6_false_of_suz hS hna e hσ hD hDm
    · exact sp6_false_of_on hS hna e hσ hD hDm
    · exact sp6_false_of_co1 hS hna e hσ hD hDm
    · exact false_of_co2_component hS hna e hσ hD
    · exact sp6_false_of_co3 hS hna e hσ hD hDm
    · exact sp6_false_of_fi22 hS hna e hσ hD hDm hcase
    · exact sp6_false_of_fi23 hS hna e hσ hD hDm
    · exact sp6_false_of_fi24 hS hna e hσ hD hDm
    · exact sp6_false_of_hn hS hna e hσ hD hDm
    · exact false_of_th_component hS hna e hσ hD
    · exact sp6_false_of_baby hS hna e hσ (.inl rfl) hD hDm
  · exact sp6_false_of_baby hS hna e hσ (.inr rfl) hD hDm

end Residual

end CFSG.SeitzReduction.SporadicRefine
