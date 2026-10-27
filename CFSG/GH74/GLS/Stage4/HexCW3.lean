module

public import CFSG.GH74.GLS.Stage4.HexCMu

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem sl2_D_W (t : Fˣ) : sl2D t * sl2W F * (sl2D t)⁻¹ = sl2D (t * t) * sl2W F := by
  rw [mul_inv_eq_iff_eq_mul]
  apply sl2_ext
  have ht : (t : F) ≠ 0 := t.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_T (D : HexData root F) {n : G} (hn : n = D.φ (sl2W F)) (t : Fˣ) :
    D.T t * n * (D.T t)⁻¹ = D.T (t * t) * n := by
  have h := congrArg D.φ (sl2_D_W (F := F) t)
  simp only [map_mul, map_inv] at h
  subst hn
  simp only [D.T_eq]
  exact h

theorem weyl_lin (D : HexData root F) {n : G} (hn : n = D.φ (sl2W F)) {f : F → F}
    (hf : ∀ d, n * D.p2 d * n⁻¹ = D.p4 (f d)) (x : F) : f x = x * f 1 := by
  by_cases hx : x = 0
  · subst hx
    have h0 : D.p4 (f 0) = 1 := by
      rw [← hf, map_zero_of_add' D.p2_add]; group
    have : f 0 = 0 := D.p4_inj (by rw [h0, map_zero_of_add' D.p4_add])
    rw [this]; ring
  · obtain ⟨τ, hτ⟩ : ∃ τ : Fˣ, (τ : F) = x⁻¹ := ⟨Units.mk0 x⁻¹ (inv_ne_zero hx), rfl⟩
    have hT := weyl_T D hn τ
    have e1 : D.T τ * (n * D.p2 1 * n⁻¹) * (D.T τ)⁻¹ =
        (D.T τ * n * (D.T τ)⁻¹) * (D.T τ * D.p2 1 * (D.T τ)⁻¹) * (D.T τ * n * (D.T τ)⁻¹)⁻¹ := by
      group
    have e2 : D.T τ * (n * D.p2 1 * n⁻¹) * (D.T τ)⁻¹ = D.p4 ((τ : F) * f 1) := by
      rw [hf, D.w4]
    rw [hT, D.w2] at e1
    have e3 : (D.T (τ * τ) * n) * D.p2 ((τ : F)⁻¹ * 1) * (D.T (τ * τ) * n)⁻¹ =
        D.p4 (((τ * τ : Fˣ) : F) * f ((τ : F)⁻¹ * 1)) := by
      rw [← D.w4, ← hf]; group
    rw [e1, e3] at e2
    have e4 := D.p4_inj e2
    rw [Units.val_mul, hτ, inv_inv] at e4
    rw [mul_one] at e4
    field_simp at e4
    linear_combination e4

end CFSG.GH74.GLS.Stage4.Hex
