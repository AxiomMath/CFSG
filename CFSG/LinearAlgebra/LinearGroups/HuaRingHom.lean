module

public import Mathlib.Algebra.CharP.Reduced
import CFSG.LinearAlgebra.LinearGroups.HuaIdentity
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LinearGroups

theorem hua_ring_identity {R : Type*} [Ring R] {a a' b b' c' d' : R} (ha : a' * a = 1)
    (hb : b' * b = 1) (hc : c' * (b' - a) = 1) (hd : d' * (a' + c') = 1) :
    a - d' = a * b * a := by
  have h1 : (a' + c') * ((b' - a) * b * a) = 1 := by
    have e : (a' + c') * ((b' - a) * b * a) =
        a' * (b' * b) * a - (a' * a) * (b * a) + (c' * (b' - a)) * (b * a) := by
      noncomm_ring
    rw [e, hb, mul_one, ha, hc]
    noncomm_ring
  have h2 : d' = (b' - a) * b * a := by
    calc d' = d' * ((a' + c') * ((b' - a) * b * a)) := by rw [h1, mul_one]
      _ = (d' * (a' + c')) * ((b' - a) * b * a) := (mul_assoc _ _ _).symm
      _ = (b' - a) * b * a := by rw [hd, one_mul]
  have e : a - (b' - a) * b * a = a - (b' * b) * a + a * b * a := by noncomm_ring
  rw [h2, e, hb, one_mul, sub_self, zero_add]

theorem hua_map_sandwich {K R : Type*} [Field K] [Ring R] (f : K →+ R)
    (hinv : ∀ t : K, t ≠ 0 → f t⁻¹ * f t = 1) (a b : K) :
    f (a * b * a) = f a * f b * f a := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  by_cases hab : a * b = 1
  · have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
    subst hb'
    rw [mul_inv_cancel₀ ha, one_mul, mul_assoc, hinv a ha, mul_one]
  obtain ⟨hc, hd, he⟩ := hua_field_identity ha hb hab
  have key := hua_ring_identity (a := f a) (a' := f a⁻¹) (b := f b) (b' := f b⁻¹)
    (c' := f (b⁻¹ - a)⁻¹) (d' := f (a⁻¹ + (b⁻¹ - a)⁻¹)⁻¹) (hinv a ha) (hinv b hb)
    (by rw [← map_sub]; exact hinv _ hc) (by rw [← map_add]; exact hinv _ hd)
  have e : a * b * a = a ^ 2 * b := by ring
  rw [e, ← he, map_sub, key]

theorem hua_map_mul {K R : Type*} [Field K] [Finite K] [CharP K 2] [Ring R] (f : K →+ R)
    (h1 : f 1 = 1) (hinv : ∀ t : K, t ≠ 0 → f t⁻¹ * f t = 1) (a b : K) :
    f (a * b) = f a * f b := by
  have hsq : ∀ x, f (x * x) = f x * f x := fun x => by
    simpa [h1] using hua_map_sandwich f hinv x 1
  have h2 : (2 : R) = 0 := by
    have h : f (1 + 1) = 0 := by rw [CharTwo.add_self_eq_zero, map_zero]
    rw [map_add, h1, one_add_one_eq_two] at h
    exact h
  have hcomm : ∀ x y, f x * f y = f y * f x := fun x y => by
    have e1 : f ((x + y) * (x + y)) = f (x * x) + f (y * y) := by
      rw [← map_add]
      congr 1
      linear_combination (x * y) * (CharTwo.two_eq_zero (R := K))
    rw [hsq, hsq, hsq, map_add] at e1
    have e2 : f x * f y + f y * f x = 0 := by
      have e3 : (f x + f y) * (f x + f y) =
          f x * f x + f y * f y + (f x * f y + f y * f x) := by noncomm_ring
      rw [e3] at e1
      exact add_eq_left.mp e1
    have e4 : f y * f x + f y * f x = 0 := by rw [← two_mul, h2, zero_mul]
    calc f x * f y = -(f y * f x) := eq_neg_of_add_eq_zero_left e2
      _ = f y * f x := (eq_neg_of_add_eq_zero_left e4).symm
  obtain ⟨c, rfl⟩ := isSquare_of_charTwo' a
  calc f (c * c * b) = f (c * b * c) := by congr 1; ring
    _ = f c * f b * f c := hua_map_sandwich f hinv c b
    _ = f c * f c * f b := by rw [mul_assoc, hcomm b c, ← mul_assoc]
    _ = f (c * c) * f b := by rw [hsq]

@[expose] def huaRingHom {K R : Type*} [Field K] [Finite K] [CharP K 2] [Ring R] (f : K →+ R)
    (h1 : f 1 = 1) (hinv : ∀ t : K, t ≠ 0 → f t⁻¹ * f t = 1) : K →+* R where
  toFun := f
  map_one' := h1
  map_mul' := hua_map_mul f h1 hinv
  map_zero' := f.map_zero
  map_add' := f.map_add

@[simp] theorem huaRingHom_apply {K R : Type*} [Field K] [Finite K] [CharP K 2] [Ring R]
    (f : K →+ R) (h1 : f 1 = 1) (hinv : ∀ t : K, t ≠ 0 → f t⁻¹ * f t = 1) (a : K) :
    huaRingHom f h1 hinv a = f a :=
  rfl

end CFSG.LinearGroups
