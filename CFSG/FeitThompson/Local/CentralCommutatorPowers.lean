module
public import Mathlib.GroupTheory.Commutator.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped commutatorElement

namespace CFSG.FeitThompson

variable {P : Type*} [Group P] {x y : P}

theorem commutatorElement_inv_inv (x y : P) : ⁅x⁻¹, y⁻¹⁆ = x⁻¹ * y⁻¹ * x * y := by
  simp [commutatorElement_def]

theorem commutatorElement_pow_left_of_commute (h : Commute x ⁅x, y⁆) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' x n, commutatorElement_mul_left_eq_conj_mul, ih, (h.pow_right n).eq,
      mul_inv_cancel_right, pow_succ]

theorem commutatorElement_pow_right_of_commute (h : Commute y ⁅x, y⁆) (n : ℕ) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ y n, commutatorElement_mul_right_eq_mul_conj, ih, mul_assoc (⁅x, y⁆ ^ n),
      (h.pow_left n).eq, ← mul_assoc, mul_inv_cancel_right, pow_succ]

theorem commutatorElement_pow_left_of_mem_center (h : ⁅x, y⁆ ∈ Subgroup.center P) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n :=
  commutatorElement_pow_left_of_commute (Subgroup.mem_center_iff.mp h x) n

theorem commutatorElement_pow_right_of_mem_center (h : ⁅x, y⁆ ∈ Subgroup.center P) (n : ℕ) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n :=
  commutatorElement_pow_right_of_commute (Subgroup.mem_center_iff.mp h y) n

theorem commutatorElement_pow_left_eq_pow_right_of_mem_center
    (h : ⁅x, y⁆ ∈ Subgroup.center P) (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y ^ n⁆ :=
  (commutatorElement_pow_left_of_mem_center h n).trans
    (commutatorElement_pow_right_of_mem_center h n).symm

theorem inv_mul_inv_mul_mul_pow_left_of_mem_center
    (h : x⁻¹ * y⁻¹ * x * y ∈ Subgroup.center P) (n : ℕ) :
    (x ^ n)⁻¹ * y⁻¹ * x ^ n * y = (x⁻¹ * y⁻¹ * x * y) ^ n := by
  rw [← commutatorElement_inv_inv] at h
  rw [show (x ^ n)⁻¹ * y⁻¹ * x ^ n * y = ⁅x⁻¹ ^ n, y⁻¹⁆ by
        simp [commutatorElement_def, inv_pow],
    commutatorElement_pow_left_of_mem_center h n, commutatorElement_inv_inv]

theorem inv_mul_inv_mul_mul_pow_right_of_mem_center
    (h : x⁻¹ * y⁻¹ * x * y ∈ Subgroup.center P) (n : ℕ) :
    x⁻¹ * (y ^ n)⁻¹ * x * y ^ n = (x⁻¹ * y⁻¹ * x * y) ^ n := by
  rw [← commutatorElement_inv_inv] at h
  rw [show x⁻¹ * (y ^ n)⁻¹ * x * y ^ n = ⁅x⁻¹, y⁻¹ ^ n⁆ by
        simp [commutatorElement_def, inv_pow],
    commutatorElement_pow_right_of_mem_center h n, commutatorElement_inv_inv]

theorem inv_mul_inv_mul_mul_pow_left_eq_pow_right_of_mem_center
    (h : x⁻¹ * y⁻¹ * x * y ∈ Subgroup.center P) (n : ℕ) :
    (x ^ n)⁻¹ * y⁻¹ * x ^ n * y = x⁻¹ * (y ^ n)⁻¹ * x * y ^ n :=
  (inv_mul_inv_mul_mul_pow_left_of_mem_center h n).trans
    (inv_mul_inv_mul_mul_pow_right_of_mem_center h n).symm

end CFSG.FeitThompson
