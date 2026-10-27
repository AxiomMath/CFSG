module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTable

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (transportAut transportAut_mul_self
  transportAut_not_mem_inner fixSubTransportEquiv mem_inner_of_mulEquiv
  compsSatisfy_centralizer_of_mulEquiv isoInvariant_not_three_dvd isoInvariant_card_dvd)

theorem three_dvd_card_of_card_quotient_center_2520 {G : Type*} [Group G] {D : Subgroup G}
    (hcard : Nat.card (D ⧸ center D) = 2520) : 3 ∣ Nat.card D :=
  (show 3 ∣ 2520 by norm_num).trans (hcard ▸ card_quotient_dvd_card _)

theorem card_quotient_center_dvd_card_group {S : Type} [Group S] {σ : MulAut S}
    (D : Subgroup (fixedSubgroup σ)) : Nat.card (D ⧸ center D) ∣ Nat.card S :=
  (SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D).trans
    (card_subgroup_dvd_card _)

section M22


theorem m22_false_2520 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M22) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 2520) : False := by
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs := SeitzReduction.SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
    let φ := MulEquiv.subgroupCongr
      (SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
    have h : Nat.card (D.map φ.toMonoidHom) ∣ 384 :=
      compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M22 (isoInvariant_card_dvd 384)
        CFSG.ComponentClassification.RestrictedStd.Spor.m22_centralizerIn_comps e s hs _
        (CFSG.LocalCores.isComponent_map_mulEquiv φ hD)
    rw [card_map_of_injective φ.injective] at h
    have h2 : 2520 ∣ 384 := hcard ▸ (card_quotient_dvd_card _).trans h
    norm_num at h2
  · have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    let φ := (MulEquiv.subgroupCongr
      (SeitzReduction.SporadicRefine.fixedSubgroup_eq_fixSub' σ)).trans
      (fixSubTransportEquiv e σ)
    have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
      CFSG.ComponentClassification.RestrictedStd.Spor.m22_outer_comps (transportAut e σ)
        (transportAut_mul_self e hσ2) (transportAut_not_mem_inner e hin) _
        (CFSG.LocalCores.isComponent_map_mulEquiv φ hD)
    rw [card_map_of_injective φ.injective] at h
    exact h (three_dvd_card_of_card_quotient_center_2520 hcard)

end M22

section M23


theorem m23_false_2520 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 2520) : False := by
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e (fun β => by
    obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m23_all_inner β
    exact ⟨h, hh.symm⟩) σ
  have hs := SeitzReduction.SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
  let φ := MulEquiv.subgroupCongr
    (SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M23 isoInvariant_not_three_dvd
      CFSG.ComponentClassification.RestrictedStd.Spor.m23_centralizerIn_comps e s hs _
      (CFSG.LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_card_quotient_center_2520 hcard)

end M23

section M24


theorem m24_false_2520 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M24) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 2520) : False := by
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e (fun β => by
    obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m24_all_inner β
    exact ⟨h, hh.symm⟩) σ
  have hs := SeitzReduction.SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
  let φ := MulEquiv.subgroupCongr
    (SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M24 isoInvariant_not_three_dvd
      CFSG.ComponentClassification.RestrictedStd.Spor.m24_centralizerIn_comps e s hs _
      (CFSG.LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_card_quotient_center_2520 hcard)

end M24

section J2


theorem j2_false_2520 {S : Type} [Group S] (e : S ≃* NativeSporadic.J2) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hcard : Nat.card (D ⧸ center D) = 2520) : False := by
  set θ := e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hc : Nat.card (fixedSubgroup σ) =
      Nat.card (CFSG.Sporadic.Schreier.fixSub (transportAut θ σ)) :=
    Nat.card_congr ((MulEquiv.subgroupCongr
      (SeitzReduction.SporadicRefine.fixedSubgroup_eq_fixSub' σ)).trans
      (fixSubTransportEquiv θ σ)).toEquiv
  have hdvd := SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
  rw [hcard, hc] at hdvd
  rcases CFSG.QuasithinUnique.Id2519.Tab.j2_fixSub_card (transportAut θ σ)
      (transportAut_mul_self θ hσ2)
      (SeitzReduction.SporadicRefine.transportAut_ne_one θ hσ) with h | h | h <;>
    rw [h] at hdvd <;> norm_num at hdvd

end J2

section He


theorem he_outer_fixedSubgroup_card {S : Type} [Group S]
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nat.card (fixedSubgroup σ) = 15120 :=
  SeitzReduction.SporadicRefine.he_outer_card_fixedSubgroup e hσ hout

end He

section Orders

theorem card_carrier_M11 :
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 :=
  CFSG.Sporadic.Mathieu.card_M11

theorem card_carrier_M12 :
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M12) = 95040 :=
  CFSG.Sporadic.Mathieu.card_M12

theorem card_carrier_J1 :
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J1) = 175560 :=
  CFSG.Sporadic.J1.card_J1

theorem card_carrier_J3 :
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J3) = 50232960 :=
  CFSG.Sporadic.J3.card_J3

end Orders

section Rows


theorem sporadic_comp_2520 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : CFSG.IsComponent D)
    (h : Nat.card (↥D ⧸ Subgroup.center ↥D) = 2520) :
    s = .He ∧ σ ∉ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨hin, hout⟩ := sporadic_comp_rows hS hna e hσ hD
  rw [h] at hin hout
  cases s
  case M11 =>
    have hd := card_quotient_center_dvd_card_group D
    rw [h, Nat.card_congr e.toEquiv, card_carrier_M11] at hd
    norm_num at hd
  case M12 =>
    have hd := card_quotient_center_dvd_card_group D
    rw [h, Nat.card_congr e.toEquiv, card_carrier_M12] at hd
    norm_num at hd
  case M22 => exact (m22_false_2520 hS hna e hσ hD h).elim
  case M23 => exact (m23_false_2520 hS hna e hσ hD h).elim
  case M24 => exact (m24_false_2520 hS hna e hσ hD h).elim
  case J1 =>
    have hd := card_quotient_center_dvd_card_group D
    rw [h, Nat.card_congr e.toEquiv, card_carrier_J1] at hd
    norm_num at hd
  case J2 => exact (j2_false_2520 e hσ h).elim
  case J3 =>
    have hd := card_quotient_center_dvd_card_group D
    rw [h, Nat.card_congr e.toEquiv, card_carrier_J3] at hd
    norm_num at hd
  case He =>
    refine ⟨rfl, fun hm => ?_⟩
    have h20 : (2520 : ℕ) = 20160 := hin hm
    omega
  all_goals
    by_cases hm : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact absurd (hin hm) (by norm_num [SporadicInnerRow])
    · exact absurd (hout hm) (by norm_num [SporadicOuterRow])

end Rows

end CFSG.ComponentClassification.CatFC
