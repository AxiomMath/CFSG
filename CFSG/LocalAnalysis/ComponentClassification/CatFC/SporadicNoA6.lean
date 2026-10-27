module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicNoA7
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporM12J2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (transportAut transportAut_mul_self
  transportAut_not_mem_inner fixSubTransportEquiv mem_inner_of_mulEquiv
  compsSatisfy_centralizer_of_mulEquiv isoInvariant_not_three_dvd isoInvariant_card_dvd)

theorem three_dvd_card_of_card_quotient_center_360 {G : Type*} [Group G] {D : Subgroup G}
    (hcard : Nat.card (D ⧸ center D) = 360) : 3 ∣ Nat.card D :=
  (show 3 ∣ 360 by norm_num).trans (hcard ▸ card_quotient_dvd_card _)

section Fixed


theorem card_fixedSubgroup_m11 {S : Type} [Group S] (e : S ≃* NativeSporadic.M11)
    {σ : MulAut S} (hσ : orderOf σ = 2) : Nat.card (fixedSubgroup σ) = 48 := by
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hα2 : MulAut.congr e σ * MulAut.congr e σ = 1 := by
    rw [← map_mul, hσ2, map_one]
  have hα1 : MulAut.congr e σ ≠ 1 := fun h =>
    hσ1 ((MulAut.congr e).injective (by rw [map_one]; exact h))
  rw [show Nat.card (fixedSubgroup σ) = Nat.card ↥(CFSG.GH74.Uniqueness.Bender.autFixed σ)
      from rfl, ← CFSG.GH74.Generic.S45.card_fixed_congr' e σ]
  exact CFSG.GH74.Generic.S45.LAlt.m11_fixed_card _ hα2 hα1

end Fixed

section M12


theorem card_fixedSubgroup_m12 {S : Type} [Group S] (e : S ≃* NativeSporadic.M12)
    {σ : MulAut S} (hσ : orderOf σ = 2) :
    Nat.card (fixedSubgroup σ) = 120 ∨ Nat.card (fixedSubgroup σ) = 192 ∨
      Nat.card (fixedSubgroup σ) = 240 := by
  have hα : orderOf (MulAut.congr e σ) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hσ
  rw [show Nat.card (fixedSubgroup σ) = Nat.card ↥(CFSG.GH74.Uniqueness.Bender.autFixed σ)
      from rfl, ← CFSG.GH74.Generic.S45.card_fixed_congr' e σ]
  exact CFSG.GH74.GLS.IVK.Proofs2.m12_fixed_card_aut _ hα

end M12

section J3


theorem card_fixedSubgroup_j3 {S : Type} [Group S] (e : S ≃* NativeSporadic.J3)
    {σ : MulAut S} (hσ : orderOf σ = 2) :
    Nat.card (fixedSubgroup σ) = 1920 ∨ Nat.card (fixedSubgroup σ) = 2448 := by
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  rw [show Nat.card (fixedSubgroup σ) = Nat.card ↥(CFSG.GH74.Uniqueness.Bender.autFixed σ)
      from rfl]
  exact CFSG.GH74.Generic.S45.j3_fixed_card e σ hσ2 hσ1

end J3

section M22


theorem m22_false_360 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M22) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 360) : False := by
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
    have h2 : 360 ∣ 384 := hcard ▸ (card_quotient_dvd_card _).trans h
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
    exact h (three_dvd_card_of_card_quotient_center_360 hcard)

end M22

section M23


theorem m23_false_360 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 360) : False := by
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
  exact h (three_dvd_card_of_card_quotient_center_360 hcard)

end M23

section M24


theorem m24_false_360 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M24) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 360) : False := by
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
  exact h (three_dvd_card_of_card_quotient_center_360 hcard)

end M24

section J2


theorem j2_false_360 {S : Type} [Group S] (e : S ≃* NativeSporadic.J2) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hcard : Nat.card (D ⧸ center D) = 360) : False := by
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

section HS


theorem hs_card_centralizer_ne_720 {S : Type} [Group S] [Finite S]
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier .HS) (z : S) (hz : orderOf z = 2) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set S)) ≠ 720 := by
  intro h
  rcases CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_involution_hs
    ⟨e⟩ z hz with h1 | h1 <;> omega

end HS

section Rows


theorem sporadic_comp_360 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : CFSG.IsComponent D)
    (h : Nat.card (↥D ⧸ Subgroup.center ↥D) = 360) :
    (s = .HS ∧ σ ∈ (MulAut.conj : S →* MulAut S).range) ∨
      (s = .He ∧ σ ∉ (MulAut.conj : S →* MulAut S).range) := by
  obtain ⟨hin, hout⟩ := sporadic_comp_rows hS hna e hσ hD
  rw [h] at hin hout
  cases s
  case M11 =>
    have hd := SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
    rw [h, card_fixedSubgroup_m11 e hσ] at hd
    norm_num at hd
  case M12 =>
    have hd := SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
    rw [h] at hd
    rcases card_fixedSubgroup_m12 e hσ with hc | hc | hc <;> rw [hc] at hd <;> norm_num at hd
  case M22 => exact (m22_false_360 hS hna e hσ hD h).elim
  case M23 => exact (m23_false_360 hS hna e hσ hD h).elim
  case M24 => exact (m24_false_360 hS hna e hσ hD h).elim
  case J1 =>
    have hd := card_quotient_center_dvd_card_group D
    rw [h, Nat.card_congr e.toEquiv, card_carrier_J1] at hd
    norm_num at hd
  case J2 => exact (j2_false_360 e hσ h).elim
  case J3 =>
    have hd := SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
    rw [h] at hd
    rcases card_fixedSubgroup_j3 e hσ with hc | hc <;> rw [hc] at hd <;> norm_num at hd
  case HS =>
    by_cases hm : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact Or.inl ⟨rfl, hm⟩
    · exact absurd (hout hm) (by norm_num [SporadicOuterRow])
  case He =>
    by_cases hm : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact absurd (hin hm) (by norm_num [SporadicInnerRow])
    · exact Or.inr ⟨rfl, hm⟩
  all_goals
    by_cases hm : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact absurd (hin hm) (by norm_num [SporadicInnerRow])
    · exact absurd (hout hm) (by norm_num [SporadicOuterRow])

end Rows

end CFSG.ComponentClassification.CatFC
