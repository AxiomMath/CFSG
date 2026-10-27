module

public import CFSG.LargeExtraspecial.DWCaseIIBDich

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem hypFun_ρ (hWs : ∀ v ∈ spanD S, S.q v = 0) (m : S.M) {u v : S.Qt} (hu : u ∈ spanD S)
    (hv : v ∈ spanD S) :
    hypFun (axisV S) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
      (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = hypFun (axisV S) u v :=
  hypFun_apply_apply (U := spanD S) ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap
    (fun _ _ hv0 e => hv0 ((LinearEquiv.map_eq_zero_iff _).mp e))
    (fun u _ _ hv hv0 => (mem_axisV_ρ_iff hWs m hv hv0 u).symm) hu hv

theorem two_le_card_of_mem {U : Submodule (ZMod 2) S.Qt} {v : S.Qt} (hv : v ∈ U) (hv0 : v ≠ 0) :
    2 ≤ Nat.card U := by
  have := finiteDimensional_Qt (S := S)
  rw [S.card_submodule]
  have : finrank (ZMod 2) U ≠ 0 := fun h => hv0 (by
    rw [Submodule.finrank_eq_zero] at h
    rw [h] at hv
    exact (Submodule.mem_bot _).mp hv)
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ finrank (ZMod 2) U := Nat.pow_le_pow_right two_pos (Nat.one_le_iff_ne_zero.mpr this)

namespace MaxEA

variable {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
  (hM : S.M ≤ normalizer (A : Set G))
  (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
  (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
  {g : G} (hxA : g * S.z * g⁻¹ ∈ A) (hxz : g * S.z * g⁻¹ ≠ S.z)
include hA hM hII hxA hxz

theorem Lbar_sub_mem_axisD {t : S.O} (ht : t ∈ S.Lbar g) {w : S.Qt} (hw : w ∈ spanD S) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ axisD S g := by
  rw [hA.axisD_eq hII hxA hxz]
  refine ⟨hA.Lbar_sub_mem_axisA hM hII hxA ht (spanD_le_clSub hII hw), sub_mem ?_ hw⟩
  obtain ⟨k, hk, rfl⟩ := mem_Lbar.mp ht
  exact isMbarInvariant_spanD _ w hw

omit hM in
theorem Lbar_sub_mem_span' {t : S.O} (ht : t ∈ S.Lbar g) {u : S.Qt} (hu : u ∈ axisD S g) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  rw [hA.axisD_eq hII hxA hxz] at hu
  exact hA.Lbar_sub_mem_span ht hu.1

theorem two_mul_card_Lbar_le (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z →
      ¬ A ≤ S.Qa g) :
    2 * Nat.card (S.Lbar g) ≤ Nat.card (spanD S) := by
  have := finiteDimensional_Qt (S := S)
  have hWs := q_spanD hII
  have hxQ := hA.le_QG hxA
  have hx0 : S.cl (g * S.z * g⁻¹) ≠ 0 := (cl_ne_zero_iff hxQ).mpr hxz
  have hxD := cl_conj_mem_spanD hxQ
  have hxH : S.cl (g * S.z * g⁻¹) ∈ axisD S g := cl_mem_axisD_self hxQ
  rcases hA.finrank_axisD_le_one_or hM hII hbad hxA hxz with hsl | hsp
  ·
    have hax : axisD S g = ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
      refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr
        hxH) ?_).symm
      rw [finrank_span_singleton hx0]
      exact hsl
    set T := (S.Lbar g).map S.O.subtype
    have hTW : ∀ t ∈ T, ∀ w ∈ spanD S, t w - w ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
      rintro _ ⟨t, ht, rfl⟩ w hw
      rw [← hax]
      exact hA.Lbar_sub_mem_axisD hM hII hxA hxz ht hw
    have hinj : ∀ t ∈ T, (∀ w ∈ spanD S, t w = w) → t = 1 := by
      rintro _ ⟨t, ht, rfl⟩ hfix
      rw [hA.Lbar_eq_one_of_fix_spanD hM hII hxA hxz ht hfix]
      rfl
    have hcount := card_mul_card_fixIn_le hx0 hTW hinj
    have hT : Nat.card T = Nat.card (S.Lbar g) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    have hfix : 2 ≤ Nat.card (fixIn T (spanD S)) := two_le_card_of_mem
      ⟨hxD, fun t ht => by
        obtain ⟨t, ht, rfl⟩ := ht
        exact Lbar_apply_cl hxQ ht⟩ hx0
    rw [hT] at hcount
    nlinarith
  ·
    have hfam := hA.isHypFamily_axisV hM hII hbad hxA hxz hsp
    have hne := hA.axisV_ne hM hII hbad hxD hx0
    rw [axisV_cl hWs hxQ hxz] at hne
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (axisD_le_spanD g) hne)
    obtain ⟨y, hyD, hyH⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne (axisD_le_spanD g) hne)
    have hsup : axisD S g ⊔ ZMod 2 ∙ y = spanD S :=
      Submodule.eq_of_le_of_finrank_eq (sup_le (axisD_le_spanD g)
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hyD))
        (by rw [finrank_sup_span_singleton hyH]; omega)
    have hxy : hypFun (axisV S) (S.cl (g * S.z * g⁻¹)) y = 1 := by
      rw [hfam.hypFun_symm hxD hyD, hypFun_eq_one_iff, axisV_cl hWs hxQ hxz]
      exact ⟨hx0, hyH⟩
    let Φ : S.Lbar g → axisD S g := fun t =>
      ⟨((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y, hA.Lbar_sub_mem_axisD hM hII hxA hxz t.2 hyD⟩
    have hΦ : Function.Injective Φ := by
      intro t₁ t₂ he
      have he' : ((t₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y = ((t₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y :=
        sub_left_injective (congrArg Subtype.val he)
      set t := t₂⁻¹ * t₁
      have hty : ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y = y := by
        change ((t₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm
          (((t₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) = y
        rw [he', LinearEquiv.symm_apply_apply]
      obtain ⟨k, hk, hkt⟩ := mem_Lbar.mp t.2
      have hfixH : ∀ u ∈ axisD S g, ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
        intro u hu
        obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp
          (hA.Lbar_sub_mem_span' hII hxA hxz t.2 hu)
        have huD : u ∈ spanD S := axisD_le_spanD g hu
        have hinv := hypFun_ρ hWs ⟨k, hk.2⟩ huD hyD
        rw [hkt, hty, show ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
          u + μ • S.cl (g * S.z * g⁻¹) by rw [hμ]; abel] at hinv
        rcases zmod2_dichotomy μ with rfl | rfl
        · rw [zero_smul] at hμ
          exact (sub_eq_zero.mp hμ.symm)
        · exfalso
          rw [one_smul, hfam.hypFun_add_left huD hxD hyD, hxy] at hinv
          have := congrArg (· - hypFun (axisV S) u y) hinv
          simp at this
      have ht1 : (t : S.O) = 1 := by
        refine hA.Lbar_eq_one_of_fix_spanD hM hII hxA hxz t.2 fun w hw => ?_
        rw [← hsup] at hw
        obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
        obtain ⟨ν, rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [map_add, map_smul, hfixH u hu, hty]
      exact (inv_mul_eq_one.mp (Subtype.ext ht1 : t₂⁻¹ * t₁ = 1)).symm
    have h1 := Nat.card_le_card_of_injective Φ hΦ
    rw [S.card_submodule (axisD S g)] at h1
    rw [S.card_submodule (spanD S), show finrank (ZMod 2) (spanD S) =
      finrank (ZMod 2) (axisD S g) + 1 by omega, pow_succ]
    omega

theorem spanD_eq_clSub (h1 : 1 ≤ S.width) (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A →
      g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g) :
    spanD S = S.clSub A := by
  have := finiteDimensional_Qt (S := S)
  have hb := hA.two_mul_card_Lbar_le hM hII hxA hxz hbad
  have hL := S.card_Lbar_ge (hA.le_QG hxA) hxz
  rw [S.card_submodule] at hb
  have h2 : 2 ^ S.width ≤ 2 ^ finrank (ZMod 2) (spanD S) := by
    calc 2 ^ S.width = 2 * 2 ^ (S.width - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ _ := le_trans (Nat.mul_le_mul_left 2 hL) hb
  have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hle := spanD_le_clSub hII
  refine Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle) ?_)
  rw [hA.finrank_clSub]
  exact h3

end MaxEA

end CFSG.LargeExtraspecial.DW
