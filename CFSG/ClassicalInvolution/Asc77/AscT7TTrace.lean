module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.ClassicalInvolution.Asc77.T7T

open scoped MatrixGroups

variable {F : Type} [Field F]

theorem sq_eq_trace_smul_sub_det (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring

theorem det_sub_one {w : Matrix (Fin 2) (Fin 2) F} (hw : w.det = 1) :
    (w - 1).det = 2 - w.trace := by
  rw [Matrix.det_fin_two] at hw ⊢
  simp [Matrix.trace_fin_two] at hw ⊢
  linear_combination hw


theorem one_add_pow_of_sq_eq_zero {N : Matrix (Fin 2) (Fin 2) F} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : F) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have : N * N = 0 := hN
    calc (1 + (k : F) • N) * (1 + N) = 1 + N + (k : F) • N + (k : F) • (N * N) := by
          simp [mul_add, add_mul]
          abel
      _ = 1 + ((k + 1 : ℕ) : F) • N := by
          rw [this, smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul]
          abel

theorem eq_or_mul_eq_one_of_trace_eq {x y : SL(2, F)} (h2 : (2 : F) ≠ 0) {m : ℕ}
    (hx : x ^ (2 ^ m) = 1) (hy : y ^ (2 ^ m) = 1) (hxy : x * y = y * x)
    (ht : (x : Matrix (Fin 2) (Fin 2) F).trace = (y : Matrix (Fin 2) (Fin 2) F).trace) :
    y = x ∨ x * y = 1 := by
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hX
  set Y : Matrix (Fin 2) (Fin 2) F := (y : Matrix (Fin 2) (Fin 2) F) with hY
  have hXY : X * Y = Y * X := by
    have := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) hxy
    simpa using this
  have hXd : X.det = 1 := x.det_coe
  have hYd : Y.det = 1 := y.det_coe
  have hXc := sq_eq_trace_smul_sub_det X
  have hYc := sq_eq_trace_smul_sub_det Y
  rw [hXd, one_smul] at hXc
  rw [hYd, one_smul] at hYc
  rw [← ht] at hYc
  set t := X.trace with htdef
  have key : (Y - X) * (X * Y - 1) = 0 := by
    have e1 : (Y - X) * (X * Y - 1) = Y * (X * Y) - Y - X * (X * Y) + X := by noncomm_ring
    have e2 : Y * (X * Y) = X * (Y * Y) := by rw [← Matrix.mul_assoc, ← hXY, Matrix.mul_assoc]
    rw [e1, e2, hYc, ← Matrix.mul_assoc X X Y, hXc]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one, Matrix.one_mul]
    abel
  by_cases hdet : (X * Y - 1).det = 0
  · right
    set W : Matrix (Fin 2) (Fin 2) F := X * Y with hW
    have hWd : W.det = 1 := by rw [hW, Matrix.det_mul, hXd, hYd, one_mul]
    have htr : W.trace = 2 := by
      have := det_sub_one hWd
      rw [hdet] at this
      linear_combination this
    have hWc := sq_eq_trace_smul_sub_det W
    rw [hWd, htr, one_smul] at hWc
    have hN : (W - 1) * (W - 1) = 0 := by
      have : (W - 1) * (W - 1) = W * W - 2 • W + 1 := by noncomm_ring
      rw [this, hWc]
      simp only [two_smul, ofNat_smul_eq_nsmul]
      abel
    have hWpow : W ^ (2 ^ m) = 1 := by
      have h1 : (x * y) ^ (2 ^ m) = 1 := by
        have hc : Commute x y := hxy
        rw [hc.mul_pow, hx, hy, one_mul]
      have := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) h1
      simpa [hW, hX, hY] using this
    have hexp : W ^ (2 ^ m) = 1 + ((2 ^ m : ℕ) : F) • (W - 1) := by
      have := one_add_pow_of_sq_eq_zero hN (2 ^ m)
      rwa [add_sub_cancel] at this
    rw [hexp] at hWpow
    have h0 : ((2 ^ m : ℕ) : F) • (W - 1) = 0 := by
      have := hWpow
      simpa using this
    have hne : ((2 ^ m : ℕ) : F) ≠ 0 := by
      simpa using pow_ne_zero m h2
    have hW1 : W - 1 = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd h hne
      · exact h
    apply Subtype.ext
    simpa [sub_eq_zero, hW] using hW1
  · left
    have hunit : IsUnit (X * Y - 1) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hdet
    have : Y - X = 0 := by
      obtain ⟨u, hu⟩ := hunit
      have h1 : (Y - X) * (u : Matrix (Fin 2) (Fin 2) F) = 0 := by rw [hu]; exact key
      have h2 := congrArg
        (fun M => M * ((u⁻¹ : (Matrix (Fin 2) (Fin 2) F)ˣ) : Matrix (Fin 2) (Fin 2) F)) h1
      simpa [Matrix.mul_assoc] using h2
    apply Subtype.ext
    exact sub_eq_zero.mp this


theorem eq_or_eq_inv_of_conj_mem_zpowers {x y : SL(2, F)} (h2 : (2 : F) ≠ 0) {m : ℕ}
    (hx : x ^ (2 ^ m) = 1) (hy : y ∈ Subgroup.zpowers x) (g : GL (Fin 2) F)
    (hg : (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (y : Matrix (Fin 2) (Fin 2) F)) :
    y = x ∨ y = x⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hxy : x * x ^ k = x ^ k * x := ((Commute.refl x).zpow_right k).eq
  have hyo : (x ^ k) ^ (2 ^ m) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have htr : (x : Matrix (Fin 2) (Fin 2) F).trace =
      ((x ^ k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [← hg, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    have : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mul]
  rcases eq_or_mul_eq_one_of_trace_eq h2 hx hyo hxy htr with h | h
  · left; exact h
  · right
    exact eq_inv_of_mul_eq_one_right h

end CFSG.ClassicalInvolution.Asc77.T7T
