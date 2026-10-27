module

public import CFSG.GF2Type.Smith1979.W4InspDefs
public import CFSG.GF2Type.Smith1979.W4InspOmegaA
public import CFSG.GF2Type.Smith1979.W4InspOmegaB
public import CFSG.GF2Type.Smith1979.W4C1Main
public import CFSG.LargeExtraspecial.S12InspSpOOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.Blueprint
  CFSG.RankThree.OrthogonalInvolutions CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace OmegaCase

section Local

variable {S : Setting G} {g : G} {t : S.O}

theorem mem_closure_of_image {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {T : Set B} {T' : Set A} (hT : T ⊆ f '' T') {y : A}
    (hy : f y ∈ Subgroup.closure T) : y ∈ Subgroup.closure T' := by
  have h1 : Subgroup.closure T ≤ (Subgroup.closure T').map f := by
    rw [Subgroup.closure_le]
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hT hb
    exact ⟨a, Subgroup.subset_closure ha, rfl⟩
  obtain ⟨a, ha, hfa⟩ := h1 hy
  exact hf hfa ▸ ha

theorem cl_facts (hc : Ctx S g t) :
    finrank (ZMod 2) S.Qt = 8 ∧ S.cl (g * S.z * g⁻¹) ≠ 0 ∧ S.q (S.cl (g * S.z * g⁻¹)) = 0 :=
  ⟨by rw [S.finrank_Qt_eq_two_mul_width, hc.hw], S.s12_cl_ne_zero_of_conj hc.haQ hc.hne,
    (S.q_cl_eq_zero_iff hc.haQ).mpr (S.s12_conj_z_sq g)⟩

theorem exists_mem_Mbar_of_mem_omega
    (hM : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate)
    {τ : S.Qt ≃ₗ[ZMod 2] S.Qt} (hτ : τ ∈ omegaGroup S.q S.q_nondegenerate) :
    ∃ τ' : S.O, τ' ∈ S.Mbar ∧ (τ' : S.Qt ≃ₗ[ZMod 2] S.Qt) = τ := by
  rw [← hM] at hτ
  obtain ⟨τ', hτ', rfl⟩ := hτ
  exact ⟨τ', hτ', rfl⟩

theorem exists_mem_Xbar_of_mem_omega
    (hX : (S.Xbar12 g).map S.O.subtype = omegaGroup S.q S.q_nondegenerate)
    {τ : S.Qt ≃ₗ[ZMod 2] S.Qt} (hτ : τ ∈ omegaGroup S.q S.q_nondegenerate) :
    ∃ τ' : S.O, τ' ∈ S.Xbar12 g ∧ (τ' : S.Qt ≃ₗ[ZMod 2] S.Qt) = τ := by
  rw [← hX] at hτ
  obtain ⟨τ', hτ', rfl⟩ := hτ
  exact ⟨τ', hτ', rfl⟩

theorem clSub_eq_span (hc : Ctx S g t)
    (hM : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate) :
    S.clSub (S.QG ⊓ S.Qa g) = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hV, hx0, hxq⟩ := cl_facts hc
  refine eq_span_of_invariant S.q_nondegenerate hV hx0 hxq (S6.cl_mem_clSub_self hc.haQ)
    (fun v hv => S.q_eq_zero_of_mem_clSub_QG_inf_Qa hc.hne hv) fun k hk hkx v hv => ?_
  rw [← hM] at hk
  obtain ⟨m, hm, rfl⟩ := hk
  exact S6.apply_mem_clSub_of_fix hc.haQ hc.hne hm hkx hv

theorem card_Lbar_eq (hc : Ctx S g t)
    (hD : S.clSub (S.QG ⊓ S.Qa g) = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    Nat.card (S.Lbar g) = 2 ^ 6 := by
  have h := W4C1.card_Lgrp_mul S hc.haQ hc.hne hc.hw
  rw [hD, finrank_span_singleton (cl_facts hc).2.1] at h
  rw [← W4C1.card_Lgrp]
  have h2 : Nat.card (W4C1.Lgrp S g) * 2 ^ 2 = 2 ^ 6 * 2 ^ 2 := by
    rw [← pow_add, show 6 + 2 = 8 by rfl, ← h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

theorem Lbar_map_eq_pointRadical (hc : Ctx S g t)
    (hD : S.clSub (S.QG ⊓ S.Qa g) = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
    (hcard : Nat.card (S.Lbar g) = 2 ^ 6) :
    (S.Lbar g).map S.O.subtype = pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hV, hx0, hxq⟩ := cl_facts hc
  have hle : (S.Lbar g).map S.O.subtype ≤ pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    have hfix := S.s12_Lbar_apply_cl_a hc.haQ hℓ
    refine ⟨ℓ.2, hfix, fun v hv => ?_, fun v => ?_⟩
    · rw [← hD]
      exact S.s12_Lbar_apply_sub_mem hc.haQ hℓ hv
    · have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ℓ.2
        (S.cl (g * S.z * g⁻¹)) v
      rw [hfix] at h1
      change polar S.q _ ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) = 0
      rw [polar_sub_right, h1, sub_self]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_pointRadical S.q_nondegenerate hx0 hxq, hV,
    Subgroup.card_map_of_injective S.O.subtype_injective, hcard]

theorem line_of_omega (hc : Ctx S g t)
    (hM : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate) :
    ∀ u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), u ≠ 0 →
      ∃ h : S.M, ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = u := by
  intro u hu hu0
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hV, hx0, hxq⟩ := cl_facts hc
  obtain ⟨γ, hγ, hγx⟩ :=
    exists_omega_apply_eq S.q_nondegenerate hV hx0 hu0 hxq (hc.htA.2.2.2.2 u hu)
  rw [← hM] at hγ
  obtain ⟨m, ⟨h, rfl⟩, rfl⟩ := hγ
  exact ⟨h, hγx⟩

theorem rank_of_omega (hc : Ctx S g t)
    (hM : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate) : S.S12RankThree g := by
  intro h₁ h₂ h₁x h₂x hp₁ hp₂
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hV, hx0, hxq⟩ := cl_facts hc
  have hq₁ : S.q (((S.ρ h₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (S.ρ h₁).2]
    exact hxq
  have hq₂ : S.q (((S.ρ h₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (S.ρ h₂).2]
    exact hxq
  obtain ⟨k, hk, hkx, hky⟩ := exists_omega_fix_apply_eq S.q_nondegenerate hV hx0 hxq
    (Setting.rho_cl_ne_zero hc.haQ hc.hne h₁) (Setting.rho_cl_ne_zero hc.haQ hc.hne h₂) hq₁ hq₂
    h₁x h₂x hp₁ hp₂
  rw [← hM] at hk
  obtain ⟨m, ⟨h, rfl⟩, rfl⟩ := hk
  exact ⟨h, hkx, hky⟩

theorem exists_mem_Ebar_inter_normalizer (hc : Ctx S g t)
    (hM : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate)
    (hL : (S.Lbar g).map S.O.subtype = pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    {τ : S.Qt ≃ₗ[ZMod 2] S.Qt} (hτΩ : τ ∈ omegaGroup S.q S.q_nondegenerate)
    (hτx : τ (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) (hτA : IsTypeA S.q τ 2) :
    ∃ τ' ∈ S.Ebar12 g ∩ normalizer (S.Lbar g : Set S.O), (τ' : S.Qt ≃ₗ[ZMod 2] S.Qt) = τ := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hV, hx0, hxq⟩ := cl_facts hc
  have hn3 : 3 ≤ S.width := by rw [hc.hw]; norm_num
  obtain ⟨τ', hτ'M, rfl⟩ := exists_mem_Mbar_of_mem_omega hM hτΩ
  obtain ⟨m, hmΩ, hmτ⟩ := exists_conj_mem_pointRadical S.q_nondegenerate hV hx0 hxq hτΩ hτA
  obtain ⟨m', hm'M, rfl⟩ := exists_mem_Mbar_of_mem_omega hM hmΩ
  refine ⟨τ', ⟨⟨hτ'M, hτA, m', hm'M, ?_⟩,
    (S.mem_normalizer_Lbar_iff_fix hc.haQ hc.hne hn3 hτ'M).mpr hτx⟩, rfl⟩
  rw [← hL] at hmτ
  obtain ⟨ℓ, hℓ, hℓe⟩ := hmτ
  have : ℓ = m' * τ' * m'⁻¹ := S.O.subtype_injective hℓe
  exact this ▸ hℓ

theorem normalizer_gen_of_omega (hc : Ctx S g t)
    (hM : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate)
    (hL : (S.Lbar g).map S.O.subtype = pointRadical S.q (S.cl (g * S.z * g⁻¹))) :
    S.Xbar12 g ⊓ normalizer (S.Lbar g : Set S.O) ≤
      closure (S.Ebar12 g ∩ normalizer (S.Lbar g : Set S.O)) := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hV, hx0, hxq⟩ := cl_facts hc
  have hn3 : 3 ≤ S.width := by rw [hc.hw]; norm_num
  rintro y ⟨hyX, hyN⟩
  have hyM : y ∈ S.Mbar := Setting.Xbar12_le_Mbar hyX
  have hyfix := (S.mem_normalizer_Lbar_iff_fix hc.haQ hc.hne hn3 hyM).mp hyN
  have hyΩ : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ omegaGroup S.q S.q_nondegenerate :=
    hM ▸ ⟨y, hyM, rfl⟩
  refine mem_closure_of_image S.O.subtype S.O.subtype_injective ?_
    (stab_le_closure_isTypeA S.q_nondegenerate hV hx0 hxq _ hyΩ hyfix)
  rintro τ ⟨hτΩ, hτx, hτA⟩
  obtain ⟨τ', hτ', hτ'e⟩ := exists_mem_Ebar_inter_normalizer hc hM hL hτΩ hτx hτA
  exact ⟨τ', hτ', hτ'e⟩

theorem odd_gen_of_omega (hc : Ctx S g t)
    (hX : (S.Xbar12 g).map S.O.subtype = omegaGroup S.q S.q_nondegenerate)
    (hL : (S.Lbar g).map S.O.subtype = pointRadical S.q (S.cl (g * S.z * g⁻¹))) :
    S.Lbar g ≤
      closure {y | y ∈ S.Xbar12 g ⊓ normalizer (S.Lbar g : Set S.O) ∧ Odd (orderOf y)} := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hV, hx0, hxq⟩ := cl_facts hc
  have hn3 : 3 ≤ S.width := by rw [hc.hw]; norm_num
  intro ℓ hℓ
  have hℓR : S.O.subtype ℓ ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) := hL ▸ ⟨ℓ, hℓ, rfl⟩
  refine mem_closure_of_image S.O.subtype S.O.subtype_injective ?_
    (pointRadical_le_closure_odd S.q_nondegenerate hV hx0 hxq hℓR)
  rintro y ⟨hyΩ, hyx, hyodd⟩
  obtain ⟨y', hy'X, rfl⟩ := exists_mem_Xbar_of_mem_omega hX hyΩ
  refine ⟨y', ⟨⟨hy'X, ?_⟩, ?_⟩, rfl⟩
  · exact (S.mem_normalizer_Lbar_iff_fix hc.haQ hc.hne hn3
      (Setting.Xbar12_le_Mbar hy'X)).mpr hyx
  · have h := orderOf_injective S.O.subtype S.O.subtype_injective y'
    rw [← h]
    exact hyodd

theorem model_of_omega (hc : Ctx S g t)
    (hX : (S.Xbar12 g).map S.O.subtype = omegaGroup S.q S.q_nondegenerate)
    (hcard : Nat.card (S.Lbar g) = 2 ^ 6) :
    ∃ m : ℕ, 3 ≤ m ∧
    ((∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2), (∀ x, b x x = 0) ∧
        (∀ x, (∀ y, b x y = 0) → x = 0) ∧ Nonempty (S.Xbar12 g ≃* s12SpIsometries b) ∧
        Nat.card (S.Lbar g) = 2 ^ (2 * m - 1)) ∨
      (∃ q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2), timmesfeldNondegenerate q ∧
        Nonempty (S.Xbar12 g ≃* timmesfeldOmega q) ∧ Nat.card (S.Lbar g) = 2 ^ (2 * m - 2))) := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hV : finrank (ZMod 2) S.Qt = 2 * 4 := (cl_facts hc).1
  obtain ⟨q', hnd, -, ⟨eΩ⟩, -⟩ := Bridge.exists_fin_form S.q hV
  have e1 : S.Xbar12 g ≃* (S.Xbar12 g).map S.O.subtype :=
    (S.Xbar12 g).equivMapOfInjective S.O.subtype S.O.subtype_injective
  have e2 : (S.Xbar12 g).map S.O.subtype ≃* timmesfeldOmega S.q :=
    MulEquiv.subgroupCongr (by rw [hX, s12_timmesfeldOmega_eq S.q S.q_nondegenerate])
  exact ⟨4, by norm_num, Or.inr ⟨q', hnd ((Bridge.polarBilin_nondegenerate_iff S.q).mp
    S.q_nondegenerate), ⟨(e1.trans e2).trans eΩ⟩, hcard⟩⟩

end Local

section Simple

variable [IsSimpleGroup G] {S : Setting G} {g : G} {t : S.O}

theorem map_eq_omega_of_lieModel (hc : Ctx S g t)
    (h : LieModel (S.Xbar12 g) .POmegaPlus 4 2 1 ∨ LieModel (S.Xbar12 g) .POmegaMinus 4 2 1) :
    (S.Xbar12 g).map S.O.subtype = omegaGroup S.q S.q_nondegenerate ∧
      S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate := by
  have hw : 4 ≤ S.width := hc.hw.ge
  have h' : LieModel (S.Xbar12 g) .POmegaPlus S.width 2 1 ∨
      LieModel (S.Xbar12 g) .POmegaMinus S.width 2 1 := by
    rw [hc.hw]
    exact h
  have hX := Setting.spo_Xbar12_map_eq_omegaGroup hw h'
  have hM := Setting.spo_Mbar_map_eq_timmesfeldOmega (by omega) hX
  exact ⟨hX, by rw [hM, s12_timmesfeldOmega_eq S.q S.q_nondegenerate]⟩

end Simple

end OmegaCase

section Simple

variable [IsSimpleGroup G] {S : Setting G} {g : G} {t : S.O}

theorem case2_of_omega (hc : Ctx S g t)
    (h : LieModel (S.Xbar12 g) .POmegaPlus 4 2 1 ∨ LieModel (S.Xbar12 g) .POmegaMinus 4 2 1) :
    S.S12Case2 g t := by
  obtain ⟨hX, hM⟩ := OmegaCase.map_eq_omega_of_lieModel hc h
  have hD := OmegaCase.clSub_eq_span hc hM
  have hcard := OmegaCase.card_Lbar_eq hc hD
  have hL := OmegaCase.Lbar_map_eq_pointRadical hc hD hcard
  exact ⟨⟨OmegaCase.line_of_omega hc hM, OmegaCase.rank_of_omega hc hM,
    OmegaCase.normalizer_gen_of_omega hc hM hL, OmegaCase.odd_gen_of_omega hc hX hL⟩,
    OmegaCase.model_of_omega hc hX hcard⟩

end Simple

end CFSG.GF2Type.Smith1979.W4Insp
