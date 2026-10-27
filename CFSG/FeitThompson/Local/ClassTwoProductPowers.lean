module
public import Mathlib.Data.Nat.Choose.Basic
public import CFSG.FeitThompson.Local.CentralCommutatorPowers
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped commutatorElement

namespace CFSG.FeitThompson

variable {P : Type*} [Group P] {x y : P}

theorem succ_mul_pred_div_two (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n + n * (n - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ n 1]
  simp

theorem commutatorElement_mem_center_of_commutator_le_center
    (h : commutator P ≤ Subgroup.center P) (x y : P) : ⁅x, y⁆ ∈ Subgroup.center P :=
  h (by rw [commutator_def]; exact Subgroup.commutator_mem_commutator trivial trivial)

theorem inv_mul_inv_mul_mul_eq_commutatorElement_of_mem_center
    (h : ⁅y, x⁆ ∈ Subgroup.center P) : y⁻¹ * x⁻¹ * y * x = ⁅y, x⁆ := by
  have key : y * x = ⁅y, x⁆ * (x * y) := by rw [commutatorElement_def]; group
  calc y⁻¹ * x⁻¹ * y * x = y⁻¹ * x⁻¹ * (y * x) := by rw [mul_assoc]
    _ = y⁻¹ * x⁻¹ * (⁅y, x⁆ * (x * y)) := by rw [← key]
    _ = ⁅y, x⁆ * (y⁻¹ * x⁻¹ * (x * y)) := by
        rw [← mul_assoc, Subgroup.mem_center_iff.mp h (y⁻¹ * x⁻¹), mul_assoc]
    _ = ⁅y, x⁆ := by group

theorem pow_mul_of_mem_center (h : y⁻¹ * x⁻¹ * y * x ∈ Subgroup.center P) (n : ℕ) :
    y ^ n * x = x * y ^ n * (y⁻¹ * x⁻¹ * y * x) ^ n := by
  rw [← inv_mul_inv_mul_mul_pow_left_of_mem_center h n]
  group

theorem mul_pow_of_mem_center (h : y⁻¹ * x⁻¹ * y * x ∈ Subgroup.center P) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * (y⁻¹ * x⁻¹ * y * x) ^ (n * (n - 1) / 2) := by
  set c : P := y⁻¹ * x⁻¹ * y * x
  have hc0 : ∀ g : P, Commute c g := fun g => (Subgroup.mem_center_iff.mp h g).symm
  have hc : ∀ (k : ℕ) (g : P), Commute (c ^ k) g := fun k g => (hc0 g).pow_left k
  induction n with
  | zero => simp
  | succ n ih =>
    calc (x * y) ^ (n + 1)
        = x ^ n * y ^ n * c ^ (n * (n - 1) / 2) * (x * y) := by rw [pow_succ, ih]
      _ = x ^ n * y ^ n * (c ^ (n * (n - 1) / 2) * (x * y)) := by rw [mul_assoc]
      _ = x ^ n * y ^ n * (x * y * c ^ (n * (n - 1) / 2)) := by rw [(hc _ (x * y)).eq]
      _ = x ^ n * (y ^ n * x) * y * c ^ (n * (n - 1) / 2) := by simp only [mul_assoc]
      _ = x ^ n * (x * y ^ n * c ^ n) * y * c ^ (n * (n - 1) / 2) := by
            rw [pow_mul_of_mem_center h n]
      _ = x ^ n * x * y ^ n * (c ^ n * y) * c ^ (n * (n - 1) / 2) := by simp only [mul_assoc]
      _ = x ^ n * x * y ^ n * (y * c ^ n) * c ^ (n * (n - 1) / 2) := by rw [(hc n y).eq]
      _ = x ^ n * x * (y ^ n * y) * (c ^ n * c ^ (n * (n - 1) / 2)) := by simp only [mul_assoc]
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ ((n + 1) * (n + 1 - 1) / 2) := by
            rw [← pow_succ, ← pow_succ, ← pow_add, succ_mul_pred_div_two]

theorem mul_pow_of_commutator_le_center (h : commutator P ≤ Subgroup.center P) (x y : P)
    (n : ℕ) : (x * y) ^ n = x ^ n * y ^ n * (y⁻¹ * x⁻¹ * y * x) ^ (n * (n - 1) / 2) :=
  mul_pow_of_mem_center
    ((inv_mul_inv_mul_mul_eq_commutatorElement_of_mem_center
        (commutatorElement_mem_center_of_commutator_le_center h y x)).symm ▸
      commutatorElement_mem_center_of_commutator_le_center h y x) n

theorem mul_pow_commutatorElement_of_commutator_le_center
    (h : commutator P ≤ Subgroup.center P) (x y : P) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n * (n - 1) / 2) := by
  rw [mul_pow_of_commutator_le_center h x y n,
    inv_mul_inv_mul_mul_eq_commutatorElement_of_mem_center
      (commutatorElement_mem_center_of_commutator_le_center h y x)]

theorem mul_pow_choose_of_commutator_le_center (h : commutator P ≤ Subgroup.center P) (x y : P)
    (n : ℕ) : (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2 := by
  rw [Nat.choose_two_right, mul_pow_commutatorElement_of_commutator_le_center h]

end CFSG.FeitThompson
