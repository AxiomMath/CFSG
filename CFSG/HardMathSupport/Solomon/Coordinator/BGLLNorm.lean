module

public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

variable {F : Type*} [Field F]

theorem bgll_sigma_cube {σ : F ≃+* F} (hσ : orderOf σ = 3) (x : F) : σ (σ (σ x)) = x := by
  have h : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have := congrArg (fun f : F ≃+* F => f x) h
  simpa [pow_succ, RingAut.mul_apply] using this

theorem bgll_hilbert90 {σ : F ≃+* F} (hσ : orderOf σ = 3) {l : F}
    (hl : l * σ l * σ (σ l) = 1) : ∃ y : F, y ≠ 0 ∧ l * σ y = y := by
  have hli := CFSG.GH74.GLS.IVK.H90.sigma_pow_linearIndependent σ 3 hσ
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  by_contra hno
  push Not at hno
  have hall : ∀ θ : F, θ + l * σ θ + l * σ l * σ (σ θ) = 0 := by
    intro θ
    by_contra hθ
    apply hno (θ + l * σ θ + l * σ l * σ (σ θ)) hθ
    have h3 := bgll_sigma_cube hσ θ
    simp only [map_add, map_mul, h3]
    linear_combination (θ) * hl
  have := Fintype.linearIndependent_iff.mp hli ![1, l, l * σ l] (by
    funext u
    simp only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Fin.val_zero,
      Fin.val_one, Fin.val_two, pow_zero, pow_one, RingAut.coe_one, id_eq, Matrix.head_cons,
      Matrix.tail_cons]
    have h2 : (σ ^ 2) (u : F) = σ (σ (u : F)) := by simp [pow_succ, RingAut.mul_apply]
    rw [h2]
    have := hall (u : F)
    linear_combination this) 0
  simp at this


section Norm

variable [Finite F]

@[expose] noncomputable def bgllS (σ : F ≃+* F) : Fˣ →* Fˣ := Units.map σ.toRingHom.toMonoidHom

theorem bgllS_coe (σ : F ≃+* F) (u : Fˣ) : ((bgllS σ u : Fˣ) : F) = σ (u : F) := rfl

theorem bgllS_cube {σ : F ≃+* F} (hσ : orderOf σ = 3) (u : Fˣ) :
    bgllS σ (bgllS σ (bgllS σ u)) = u :=
  Units.ext (bgll_sigma_cube hσ _)

@[expose] noncomputable def bgllN (σ : F ≃+* F) : Fˣ →* Fˣ :=
  MonoidHom.mk' (fun u => u * bgllS σ u * bgllS σ (bgllS σ u)) (by
    intro a b
    simp only [map_mul]
    ac_rfl)

@[expose] noncomputable def bgllD (σ : F ≃+* F) : Fˣ →* Fˣ :=
  MonoidHom.mk' (fun u => bgllS σ u * u⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv]
    ac_rfl)

theorem bgll_card_range_mul_card_ker {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H) :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem bgllD_range_eq {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    (bgllD σ).range = (bgllN σ).ker := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change (bgllS σ y * y⁻¹) * bgllS σ (bgllS σ y * y⁻¹) *
      bgllS σ (bgllS σ (bgllS σ y * y⁻¹)) = 1
    simp only [map_mul, map_inv, bgllS_cube hσ]
    apply Units.ext
    have h1 : σ (y : F) ≠ 0 := (map_ne_zero σ).2 y.ne_zero
    have h2 : σ (σ (y : F)) ≠ 0 := (map_ne_zero σ).2 h1
    have h0 := y.ne_zero
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one, bgllS_coe]
    field_simp
  · intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hu' : (u : F) * σ (u : F) * σ (σ (u : F)) = 1 := by
      have := congrArg (fun v : Fˣ => (v : F)) hu
      simpa [bgllN, bgllS_coe] using this
    have hl : ((u⁻¹ : Fˣ) : F) * σ ((u⁻¹ : Fˣ) : F) * σ (σ ((u⁻¹ : Fˣ) : F)) = 1 := by
      simp only [Units.val_inv_eq_inv_val, map_inv₀]
      rw [← mul_inv, ← mul_inv, hu', inv_one]
    obtain ⟨y, hy0, hy⟩ := bgll_hilbert90 hσ hl
    refine ⟨Units.mk0 y hy0, ?_⟩
    change bgllS σ (Units.mk0 y hy0) * (Units.mk0 y hy0)⁻¹ = u
    apply Units.ext
    simp only [Units.val_mul, bgllS_coe, Units.val_mk0, Units.val_inv_eq_inv_val]
    have h1 : σ y = (u : F) * y := by
      have := hy
      simp only [Units.val_inv_eq_inv_val] at this
      field_simp at this ⊢
      linear_combination this
    rw [h1]
    field_simp

theorem bgll_norm_surj {σ : F ≃+* F} (hσ : orderOf σ = 3) {t : F} (ht : σ t = t) (ht0 : t ≠ 0) :
    ∃ ν : F, ν ≠ 0 ∧ ν * σ ν * σ (σ ν) = t := by
  have hker : ∀ u : Fˣ, u ∈ (bgllD σ).ker ↔ bgllS σ u = u := by
    intro u
    rw [MonoidHom.mem_ker]
    change bgllS σ u * u⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one]
  have h1 := bgll_card_range_mul_card_ker (bgllD σ)
  have h2 := bgll_card_range_mul_card_ker (bgllN σ)
  rw [bgllD_range_eq hσ] at h1
  have hpos : 0 < Nat.card (bgllN σ).ker := Nat.card_pos
  have hcard : Nat.card (bgllN σ).range = Nat.card (bgllD σ).ker := by
    have : Nat.card (bgllN σ).range * Nat.card (bgllN σ).ker =
        Nat.card (bgllD σ).ker * Nat.card (bgllN σ).ker := by rw [h2, mul_comm, h1]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hle : (bgllN σ).range ≤ (bgllD σ).ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    change bgllS σ (u * bgllS σ u * bgllS σ (bgllS σ u)) *
      (u * bgllS σ u * bgllS σ (bgllS σ u))⁻¹ = 1
    simp only [map_mul, bgllS_cube hσ]
    apply Units.ext
    have h1 : σ (u : F) ≠ 0 := (map_ne_zero σ).2 u.ne_zero
    have h2 : σ (σ (u : F)) ≠ 0 := (map_ne_zero σ).2 h1
    have h0 := u.ne_zero
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one, bgllS_coe]
    field_simp
  have heq : (bgllN σ).range = (bgllD σ).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  have hmem : Units.mk0 t ht0 ∈ (bgllD σ).ker := by
    rw [hker]
    exact Units.ext ht
  rw [← heq] at hmem
  obtain ⟨ν, hν⟩ := hmem
  refine ⟨(ν : F), ν.ne_zero, ?_⟩
  have := congrArg (fun v : Fˣ => (v : F)) hν
  simpa [bgllN, bgllS_coe] using this

end Norm

end CFSG.HardMathSupport.Solomon.Coordinator
