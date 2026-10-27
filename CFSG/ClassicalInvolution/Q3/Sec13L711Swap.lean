module

public import CFSG.ClassicalInvolution.Q3.Sec13L711Def

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

namespace L711

@[expose] def quatLift (a b : G) (ha : a ^ 4 = 1) (hb : b * b = a * a)
    (hba : b * a * b⁻¹ = a⁻¹) : QuaternionGroup 2 →* G where
  toFun x := match x with
    | QuaternionGroup.a i => a ^ i.val
    | QuaternionGroup.xa i => b * a ^ i.val
  map_one' := by
    show a ^ (0 : ZMod (2 * 2)).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    have hA : ∀ i j : ZMod (2 * 2), a ^ i.val * a ^ j.val = a ^ (i + j).val := fun i j => by
      rw [← pow_add, pow_eq_pow_mod (i.val + j.val) ha, ← ZMod.val_add]
    have hB : ∀ i j : ZMod (2 * 2), a ^ (j - i).val = (a ^ i.val)⁻¹ * a ^ j.val := fun i j => by
      apply eq_inv_mul_of_mul_eq
      rw [hA, add_sub_cancel]
    have hab : a * b = b * a⁻¹ := by
      have h1 : b * a = a⁻¹ * b := mul_inv_eq_iff_eq_mul.mp hba
      calc a * b = a * (b * a) * a⁻¹ := by group
        _ = a * (a⁻¹ * b) * a⁻¹ := by rw [h1]
        _ = b * a⁻¹ := by group
    have hC : ∀ k : ℕ, a ^ k * b = b * (a ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc a ^ (k + 1) * b = a ^ k * (a * b) := by rw [pow_succ, mul_assoc]
          _ = a ^ k * b * a⁻¹ := by rw [hab, mul_assoc]
          _ = b * (a ^ k)⁻¹ * a⁻¹ := by rw [ih]
          _ = b * (a ^ (k + 1))⁻¹ := by rw [pow_succ', mul_inv_rev, mul_assoc]
    rintro (i | i) (j | j)
    · show a ^ (i + j).val = a ^ i.val * a ^ j.val
      rw [hA]
    · show b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
      rw [hB, ← mul_assoc (a ^ i.val) b, hC, mul_assoc]
    · show b * a ^ (i + j).val = b * a ^ i.val * a ^ j.val
      rw [mul_assoc, hA]
    · show a ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val = b * a ^ i.val * (b * a ^ j.val)
      have h2 : (((2 : ℕ) : ZMod (2 * 2))).val = 2 := rfl
      calc a ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val
          = a ^ (((2 : ℕ) : ZMod (2 * 2)) + (j - i)).val := by rw [add_sub_assoc]
        _ = a ^ 2 * ((a ^ i.val)⁻¹ * a ^ j.val) := by rw [← hA, h2, hB]
        _ = b * b * ((a ^ i.val)⁻¹ * a ^ j.val) := by rw [hb, sq]
        _ = b * (b * (a ^ i.val)⁻¹) * a ^ j.val := by group
        _ = b * a ^ i.val * (b * a ^ j.val) := by rw [← hC]; group

end L711

end CFSG.ClassicalInvolution.Q3.Sec13
