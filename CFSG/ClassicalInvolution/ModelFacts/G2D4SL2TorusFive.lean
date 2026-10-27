module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Torus7

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups

section Zmod

theorem zmod5_conic : ∀ κ' : ZMod 5, (∀ r : ZMod 5, κ' ≠ r * r) →
    ∃ u v : ZMod 5, u ^ 2 - κ' * v ^ 2 = 1 ∧ u ≠ 0 ∧ v ≠ 0 := by decide

theorem zmod5_three : ∀ u' : ZMod 5, u' ≠ 0 → ∃ s₁ s₃ : ZMod 5, s₁ ≠ 0 ∧ s₃ ≠ 0 ∧
    u' ^ 2 * ((s₁ + 1) * (s₃ + 1)) = 1 ∧ s₁ * s₃ ≠ 1 := by decide

theorem zmod5_neg_one : (2 : ZMod 5) * 2 = -1 := by decide

theorem zmod5_two_ne : (2 : ZMod 5) ≠ 0 := by decide

theorem zmod5_i : (2 : ZMod 5) * 2 = -1 ∧ -(2 * (2 : ZMod 5)) = 1 := by decide

end Zmod

section Five

variable {F : Type} [Field F] [Finite F]

theorem exists_ringEquiv_zmod_five (h5 : Nat.card F = 5) : Nonempty (F ≃+* ZMod 5) := by
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, h5, ZMod.card 5])⟩

theorem two_ne_zero_five (h5 : Nat.card F = 5) : (2 : F) ≠ 0 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := exists_ringEquiv_zmod_five h5
  intro h
  have := congrArg e h
  rw [map_ofNat, map_zero] at this
  exact zmod5_two_ne this

theorem exists_neg_one_square_five (h5 : Nat.card F = 5) : ∃ i : F, i * i = -1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := exists_ringEquiv_zmod_five h5
  refine ⟨e.symm 2, ?_⟩
  apply e.injective
  rw [map_mul, map_neg, map_one, RingEquiv.apply_symm_apply]
  exact zmod5_neg_one

theorem exists_sqrt_neg_one_five (h5 : Nat.card F = 5) : ∃ i : F, i * i = -1 ∧ -(2 * i) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := exists_ringEquiv_zmod_five h5
  refine ⟨e.symm 2, ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_neg, map_one, RingEquiv.apply_symm_apply]
    exact zmod5_i.1
  · apply e.injective
    rw [map_neg, map_mul, map_ofNat, RingEquiv.apply_symm_apply, map_one]
    exact zmod5_i.2

theorem exists_conic_point_five (h5 : Nat.card F = 5) {κ : F} (hκ : ∀ r : F, κ ≠ r * r) :
    ∃ u v : F, u ^ 2 - κ * v ^ 2 = 1 ∧ u ≠ 0 ∧ v ≠ 0 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := exists_ringEquiv_zmod_five h5
  obtain ⟨u', v', h, hu, hv⟩ := zmod5_conic (e κ) (fun r hr => hκ (e.symm r) (by
    apply e.injective
    rw [hr, map_mul, RingEquiv.apply_symm_apply]))
  refine ⟨e.symm u', e.symm v', ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_sub, map_pow, map_mul, map_pow, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, map_one]
    exact h
  · intro h0
    apply hu
    have := congrArg e h0
    rwa [RingEquiv.apply_symm_apply, map_zero] at this
  · intro h0
    apply hv
    have := congrArg e h0
    rwa [RingEquiv.apply_symm_apply, map_zero] at this

theorem exists_three_params_five (h5 : Nat.card F = 5) {u : F} (hu : u ≠ 0) :
    ∃ s₁ s₃ : Fˣ, u ^ 2 * (((s₁ : F) + 1) * ((s₃ : F) + 1)) = 1 ∧ (s₁ : F) * (s₃ : F) ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := exists_ringEquiv_zmod_five h5
  obtain ⟨s₁, s₃, h1, h3, h, hs⟩ := zmod5_three (e u)
    (fun h0 => hu (e.injective (by rw [h0, map_zero])))
  have h1' : e.symm s₁ ≠ 0 := fun h0 => h1 (by
    have := congrArg e h0
    rwa [RingEquiv.apply_symm_apply, map_zero] at this)
  have h3' : e.symm s₃ ≠ 0 := fun h0 => h3 (by
    have := congrArg e h0
    rwa [RingEquiv.apply_symm_apply, map_zero] at this)
  refine ⟨Units.mk0 _ h1', Units.mk0 _ h3', ?_, ?_⟩
  · simp only [Units.val_mk0]
    apply e.injective
    rw [map_mul, map_pow, map_mul, map_add, map_add, map_one, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply]
    exact h
  · simp only [Units.val_mk0]
    intro h0
    apply hs
    have := congrArg e h0
    rwa [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, map_one] at this

theorem eq_top_of_normTorus_five (h5 : Nat.card F = 5) (κ : Fˣ) (hκ : ∀ r : F, (κ : F) ≠ r * r)
    {H : Subgroup (SL2 F)} (hA : ∀ t : Fˣ, HSL t ∈ H)
    (hB : ∀ (s : Fˣ) (u v : F) (h : u ^ 2 - (κ : F) * v ^ 2 = 1),
      normTorusSL (κ : F) s u v h ∈ H) :
    H = ⊤ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_five h5
  obtain ⟨u, v, h, hu, hv⟩ := exists_conic_point_five h5 hκ
  obtain ⟨s₁, s₃, hrel, hs⟩ := exists_three_params_five h5 hu
  obtain ⟨hP10, hP01⟩ := normTorus_prod_three_entries (κ : F) u v h s₁ s₃ hrel
  set P : SL2 F := normTorusSL (κ : F) s₁ u v h * normTorusSL (κ : F) 1 u v h *
    normTorusSL (κ : F) s₃ u v h with hPdef
  have hPH : P ∈ H := H.mul_mem (H.mul_mem (hB s₁ u v h) (hB 1 u v h)) (hB s₃ u v h)
  have hdet := det_SL2 P
  have hP00 : (P : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := SL2_apply_zero_zero_ne_zero hP10
  set ρ : Fˣ := Units.mk0 _ hP00 with hρ
  have hc₀H : uSL ((P : Matrix (Fin 2) (Fin 2) F) 0 1 / (ρ : F)) ∈ H := by
    rw [← HSL_inv_mul_eq_uSL hP10 ρ rfl]
    exact H.mul_mem (hA _) hPH
  have hc₀ : (P : Matrix (Fin 2) (Fin 2) F) 0 1 / (ρ : F) ≠ 0 := by
    refine div_ne_zero ?_ ρ.ne_zero
    rw [hP01]
    exact mul_ne_zero hv (sub_ne_zero.mpr (Ne.symm hs))
  refine eq_top_of_uSL_ne_zero h2 hA hc₀ hc₀H (hB 1 u v h) ?_
  simp only [coe_normTorusSL, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
    inv_one, Units.val_one, one_mul]
  exact mul_ne_zero κ.ne_zero hv

end Five

end CFSG.ClassicalInvolution.G2D4Models
