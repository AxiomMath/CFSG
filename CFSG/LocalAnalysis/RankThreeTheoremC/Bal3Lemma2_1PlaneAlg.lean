module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type*} [Group G] {p : ℕ}

@[expose] def zmodPow (y : G) (a : ZMod p) : G := y ^ a.val

theorem zmodPow_zero (y : G) : zmodPow y (0 : ZMod p) = 1 := by
  simp [zmodPow]

theorem conj_zmodPow (g y : G) (a : ZMod p) :
    g * zmodPow y a * g⁻¹ = zmodPow (g * y * g⁻¹) a := by
  rw [zmodPow, zmodPow, conj_pow]

theorem zmodPow_mul_of_commute {y₁ y₂ : G} (h : y₁ * y₂ = y₂ * y₁) (a : ZMod p) :
    zmodPow (y₁ * y₂) a = zmodPow y₁ a * zmodPow y₂ a := by
  rw [zmodPow, zmodPow, zmodPow, (show Commute y₁ y₂ from h).mul_pow]

theorem zmodPow_comm {y₁ y₂ : G} (h : y₁ * y₂ = y₂ * y₁) (a b : ZMod p) :
    zmodPow y₁ a * zmodPow y₂ b = zmodPow y₂ b * zmodPow y₁ a :=
  ((show Commute y₁ y₂ from h).pow_pow a.val b.val).eq

@[expose] def PlaneActs (p : ℕ) (z w h : G) (M : Matrix (Fin 2) (Fin 2) (ZMod p)) : Prop :=
  h * z * h⁻¹ = zmodPow z (M 0 0) * zmodPow w (M 1 0) ∧
    h * w * h⁻¹ = zmodPow z (M 0 1) * zmodPow w (M 1 1)

theorem upper_pow (β : ZMod p) (j : ℕ) :
    (!![1, β; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ j = !![1, j * β; 0, 1] := by
  induction j with
  | zero => ext i k; fin_cases i <;> fin_cases k <;> simp
  | succ j ih =>
    rw [pow_succ, ih]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem lower_pow (γ : ZMod p) (j : ℕ) :
    (!![1, 0; γ, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ j = !![1, 0; j * γ, 1] := by
  induction j with
  | zero => ext i k; fin_cases i <;> fin_cases k <;> simp
  | succ j ih =>
    rw [pow_succ, ih]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem exp_aux (ν t : ZMod p) : t * ν⁻¹ + (ν - ν⁻¹) * t = ν * t := by ring

theorem exp_aux' (ν s : ZMod p) : s * ν⁻¹ + 0 = ν⁻¹ * s := by ring

theorem diag_pow (a d : ZMod p) (j : ℕ) :
    (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ j = !![a ^ j, 0; 0, d ^ j] := by
  induction j with
  | zero => ext i k; fin_cases i <;> fin_cases k <;> simp
  | succ j ih =>
    rw [pow_succ, ih]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

section Prime

variable [Fact p.Prime]

theorem zmodPow_one (y : G) : zmodPow y (1 : ZMod p) = y := by
  simp [zmodPow, ZMod.val_one]

theorem zmodPow_natCast {y : G} (hy : y ^ p = 1) (n : ℕ) :
    zmodPow y (n : ZMod p) = y ^ n := by
  rw [zmodPow, ZMod.val_natCast, ← pow_eq_pow_mod n hy]

theorem zmodPow_add {y : G} (hy : y ^ p = 1) (a b : ZMod p) :
    zmodPow y (a + b) = zmodPow y a * zmodPow y b := by
  rw [zmodPow, zmodPow, zmodPow, ZMod.val_add, ← pow_eq_pow_mod _ hy, pow_add]

theorem zmodPow_mul {y : G} (hy : y ^ p = 1) (a b : ZMod p) :
    zmodPow (zmodPow y a) b = zmodPow y (a * b) := by
  rw [zmodPow, zmodPow, zmodPow, ZMod.val_mul, ← pow_eq_pow_mod _ hy, ← pow_mul]

variable {z w : G}

theorem zw_mul_zw (hz : z ^ p = 1) (hw : w ^ p = 1) (hzw : z * w = w * z)
    (x₁ y₁ x₂ y₂ : ZMod p) :
    (zmodPow z x₁ * zmodPow w y₁) * (zmodPow z x₂ * zmodPow w y₂) =
      zmodPow z (x₁ + x₂) * zmodPow w (y₁ + y₂) := by
  rw [zmodPow_add hz, zmodPow_add hw]
  calc (zmodPow z x₁ * zmodPow w y₁) * (zmodPow z x₂ * zmodPow w y₂)
      = zmodPow z x₁ * (zmodPow w y₁ * zmodPow z x₂) * zmodPow w y₂ := by
        simp only [mul_assoc]
    _ = zmodPow z x₁ * (zmodPow z x₂ * zmodPow w y₁) * zmodPow w y₂ := by
        rw [zmodPow_comm hzw.symm y₁ x₂]
    _ = _ := by simp only [mul_assoc]

theorem PlaneActs.one : PlaneActs p z w (1 : G) 1 := by
  refine ⟨?_, ?_⟩ <;> simp [zmodPow_one, zmodPow_zero]

theorem PlaneActs.conj_apply (hz : z ^ p = 1) (hw : w ^ p = 1) (hzw : z * w = w * z) {h : G}
    {M : Matrix (Fin 2) (Fin 2) (ZMod p)} (hh : PlaneActs p z w h M) (a c : ZMod p) :
    h * (zmodPow z a * zmodPow w c) * h⁻¹ =
      zmodPow z (M 0 0 * a + M 0 1 * c) * zmodPow w (M 1 0 * a + M 1 1 * c) := by
  obtain ⟨h1, h2⟩ := hh
  have e : h * (zmodPow z a * zmodPow w c) * h⁻¹ =
      (h * zmodPow z a * h⁻¹) * (h * zmodPow w c * h⁻¹) := by group
  rw [e, conj_zmodPow, conj_zmodPow, h1, h2,
    zmodPow_mul_of_commute (zmodPow_comm hzw _ _), zmodPow_mul_of_commute (zmodPow_comm hzw _ _),
    zmodPow_mul hz, zmodPow_mul hw, zmodPow_mul hz, zmodPow_mul hw, zw_mul_zw hz hw hzw]

theorem PlaneActs.mul (hz : z ^ p = 1) (hw : w ^ p = 1) (hzw : z * w = w * z) {h₁ h₂ : G}
    {M₁ M₂ : Matrix (Fin 2) (Fin 2) (ZMod p)} (h₁a : PlaneActs p z w h₁ M₁)
    (h₂a : PlaneActs p z w h₂ M₂) : PlaneActs p z w (h₁ * h₂) (M₁ * M₂) := by
  obtain ⟨h21, h22⟩ := h₂a
  refine ⟨?_, ?_⟩
  · have e : h₁ * h₂ * z * (h₁ * h₂)⁻¹ = h₁ * (h₂ * z * h₂⁻¹) * h₁⁻¹ := by group
    rw [e, h21, h₁a.conj_apply hz hw hzw]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have e : h₁ * h₂ * w * (h₁ * h₂)⁻¹ = h₁ * (h₂ * w * h₂⁻¹) * h₁⁻¹ := by group
    rw [e, h22, h₁a.conj_apply hz hw hzw]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem PlaneActs.pow (hz : z ^ p = 1) (hw : w ^ p = 1) (hzw : z * w = w * z) {h : G}
    {M : Matrix (Fin 2) (Fin 2) (ZMod p)} (hh : PlaneActs p z w h M) (j : ℕ) :
    PlaneActs p z w (h ^ j) (M ^ j) := by
  induction j with
  | zero => simpa using (PlaneActs.one (z := z) (w := w) (p := p))
  | succ j ih => rw [pow_succ, pow_succ]; exact ih.mul hz hw hzw hh

end Prime

end CFSG.LocalAnalysis.RankThreeTheoremC
