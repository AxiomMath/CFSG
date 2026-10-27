module

public import CFSG.LargeExtraspecial.S4EightRes4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RC

open Module Subgroup CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem spRho_add_smul (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l s : ZMod 2)
    (h : β c (d + s • c) = 0) : spRho hβ h l = spRho hβ hcd l := by
  ext x
  rw [spRho_apply, spRho_apply, map_add, map_smul]
  match_scalars <;> (ring_nf; try reduce_mod_char)

theorem spRho_one_mul_apply (hβ : β.IsAlt) {a b e : V} (hab : β a b = 1) (hae : β a e = 0)
    (hbe : β b e = 0) (v : V) :
    (spRho hβ hae 1 * spRho hβ hbe 1) v =
      v + (β v a + β v b) • a + (β v b + β v e) • b + (β v a + β v e) • e := by
  have hba : β b a = 1 := by rw [isAlt_symm hβ, hab]
  have hea : β e a = 0 := by rw [isAlt_symm hβ, hae]
  rw [LinearEquiv.mul_apply, spRho_apply, spRho_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hba,
    hea, hbe, hβ.self_eq_zero]
  match_scalars <;> (ring_nf; try reduce_mod_char)

theorem pow_three_eq_one_of_apply (hβ : β.IsAlt) {a b e : V} (hab : β a b = 1)
    (hae : β a e = 0) (hbe : β b e = 0) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ v, g v = v + (β v a + β v b) • a + (β v b + β v e) • b + (β v a + β v e) • e) :
    g a = b ∧ g e = e ∧ g ^ 3 = 1 := by
  have hba : β b a = 1 := by rw [isAlt_symm hβ, hab]
  have hea : β e a = 0 := by rw [isAlt_symm hβ, hae]
  have heb : β e b = 0 := by rw [isAlt_symm hβ, hbe]
  have hga : g a = b := by
    rw [hg, hβ.self_eq_zero, hab, hae]
    match_scalars <;> (ring_nf; try reduce_mod_char)
  have hgb : g b = a + b + e := by
    rw [hg, hba, hβ.self_eq_zero, hbe]
    match_scalars <;> (ring_nf; try reduce_mod_char)
  have hge : g e = e := by
    rw [hg, hea, heb, hβ.self_eq_zero]
    match_scalars <;> (ring_nf; try reduce_mod_char)
  refine ⟨hga, hge, ?_⟩
  ext v
  change (g ^ 3) v = v
  have h1 := hg v
  have h2 : g (g v) = v + ((β v a + β v b) + (β v b + β v e)) • a + (β v a + β v b) • b +
      (β v b + β v e) • e := by
    rw [h1, map_add, map_add, map_add, map_smul, map_smul, map_smul, h1, hga, hgb, hge]
    match_scalars <;> (ring_nf; try reduce_mod_char)
  rw [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h2, map_add,
    map_add, map_add, map_smul, map_smul, map_smul, h1, hga, hgb, hge]
  match_scalars <;> (ring_nf; try reduce_mod_char)

variable [FiniteDimensional (ZMod 2) V]

theorem spRho_zero_mem_of_conj (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {X E : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} (ha : a ≠ 0)
    (hXI : X ≤ TauCeti.BilinForm.isometryGroup β) (hEX : E ≤ X)
    (hEU : E ≤ spPointRadical β a) (hcard : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E)
    (hτ : spTransvection β hβ a ∉ E) (htr : ∀ v : V, v ≠ 0 → ∃ x ∈ X, x a = v)
    (hnorm : ∀ x ∈ X, x a = a → x ∈ normalizer (E : Set (V ≃ₗ[ZMod 2] V)))
    {d : V} (hd : β a d = 0) (hdn : d ∉ (ZMod 2) ∙ a) (hdE : spRho hβ hd 0 ∈ E)
    {e : V} (he : β a e = 0) (heE : spRho hβ he 1 ∈ E)
    {k : V ≃ₗ[ZMod 2] V} (hk : k ∈ X) (hab : β a (k a) = 1) (hbe : β (k a) e = 0) :
    ∃ hx : β a (k⁻¹ e) = 0, spRho hβ hx 0 ∈ E := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  have hkI := TauCeti.BilinForm.mem_isometryGroup_iff.mp (hXI hk)
  have hke : k (k⁻¹ e) = e := k.apply_symm_apply e
  have hx : β a (k⁻¹ e) = 0 := by rw [← hkI a (k⁻¹ e), hke]; exact hbe
  refine ⟨hx, ?_⟩
  by_contra hxE
  have hidx : (E.subgroupOf (spPointRadical β a)).index = 2 := by
    have h1 := (E.subgroupOf (spPointRadical β a)).card_mul_index
    have h2 : Nat.card (E.subgroupOf (spPointRadical β a)) = Nat.card E := by
      rw [← card_map_of_injective (spPointRadical β a).subtype_injective, subgroupOf_map_subtype,
        inf_eq_left.mpr hEU]
    rw [h2] at h1
    have hpos : 0 < Nat.card E := Nat.card_pos
    have hne1 : (E.subgroupOf (spPointRadical β a)).index ≠ 1 := by
      intro h1'
      rw [Subgroup.index_eq_one] at h1'
      have hmem : (⟨_, spTransvection_mem_U hβ a⟩ : spPointRadical β a) ∈
          E.subgroupOf (spPointRadical β a) := by
        rw [h1']; exact mem_top _
      exact hτ hmem
    have hne0 : (E.subgroupOf (spPointRadical β a)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h3 : Nat.card E * (E.subgroupOf (spPointRadical β a)).index ≤ Nat.card E * 2 := by
      rw [h1]; linarith
    have := Nat.le_of_mul_le_mul_left h3 hpos
    omega
  have h1E : spRho hβ hx 1 ∈ E := by
    have hmul := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := ⟨spRho hβ hx 0, spRho_mem_spPointRadical hβ hx 0⟩)
      (b := ⟨_, spTransvection_mem_U hβ a⟩)).mpr
      (iff_of_false (fun h' => hxE h') (fun h' => hτ h'))
    rw [spRho_one_eq]
    exact hmul
  have hconj : k * spRho hβ hx 1 * k⁻¹ = spRho hβ hbe 1 := by
    rw [conj_spRho hβ hx 1 (hXI hk) (by rw [hke]; exact hbe)]
    exact spRho_congr hβ _ _ rfl hke rfl
  have hbX : spRho hβ hbe 1 ∈ X := by
    rw [← hconj]
    exact mul_mem (mul_mem hk (hEX h1E)) (inv_mem hk)
  obtain ⟨hga, hge, hg3⟩ := pow_three_eq_one_of_apply hβ hab he hbe
    (spRho_one_mul_apply hβ hab he hbe)
  have hgX : spRho hβ he 1 * spRho hβ hbe 1 ∈ X := mul_mem (hEX heE) hbX
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [spRho_zero_one] at heE
    exact hτ heE
  obtain ⟨r, hrX, hra⟩ := htr e he0
  set g := spRho hβ he 1 * spRho hβ hbe 1 with hgdef
  set y := r⁻¹ * g * r with hy
  have hyX : y ∈ X := mul_mem (mul_mem (inv_mem hrX) hgX) hrX
  have hya : y a = a := by
    rw [hy, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hra, hge, ← hra]
    exact r.symm_apply_apply a
  have hy3 : y ^ 3 = 1 := by
    rw [hy, show r⁻¹ * g * r = r⁻¹ * g * r⁻¹⁻¹ by rw [inv_inv], conj_pow, hg3, mul_one,
      mul_inv_cancel]
  have hy1 := eq_one_of_odd_of_apply_eq hβ hnd h4 ha hEU hcard hτ hd hdn hdE (hXI hyX) hya
    (hnorm y hyX hya) (by decide : Odd 3) hy3
  have hg1 : g = 1 := by
    have e1 : g = r * y * r⁻¹ := by rw [hy]; group
    rw [e1, hy1, mul_one, mul_inv_cancel]
  have hka : k a = a := by
    rw [← hga, hg1]
    rfl
  rw [hka, hβ.self_eq_zero] at hab
  exact zero_ne_one hab

end CFSG.LargeExtraspecial.S9.RC
