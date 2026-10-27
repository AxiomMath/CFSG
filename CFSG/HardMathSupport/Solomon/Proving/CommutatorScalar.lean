module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Solomon.Proving

theorem commutatorElement_eq_one_of_conj_pow {Y : Type*} [Group Y] {p a : ℕ} (hp : p.Prime)
    {x y g z₁ z₂ : Y} (hc : ⁅x, y⁆ ∈ Subgroup.center Y) (hz₁ : z₁ ∈ Subgroup.center Y)
    (hz₂ : z₂ ∈ Subgroup.center Y) (hx : g * x * g⁻¹ = x ^ a * z₁) (hy : g * y * g⁻¹ = y ^ a * z₂)
    (hpc : ⁅x, y⁆ ^ p = 1) (ha : ¬ p ∣ a ^ 2 - 1) : ⁅x, y⁆ = 1 := by
  set c : Y := ⁅x, y⁆ with hcdef
  have hcen : ∀ w : Y, w * c = c * w := fun w => Subgroup.mem_center_iff.mp hc w
  have hcm : ∀ (w : Y) (k : ℕ), w * c ^ k = c ^ k * w :=
    fun w k => (show Commute w c from hcen w).pow_right k
  have hxy : x * y = c * (y * x) := by
    rw [hcdef, commutatorElement_def]
    group
  have hA : ∀ m : ℕ, x ^ m * y = c ^ m * (y * x ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc x ^ (m + 1) * y = x * (x ^ m * y) := by rw [pow_succ', mul_assoc]
        _ = x * (c ^ m * (y * x ^ m)) := by rw [ih]
        _ = c ^ m * (x * (y * x ^ m)) := by rw [← mul_assoc, hcm x m, mul_assoc]
        _ = c ^ m * ((x * y) * x ^ m) := by rw [mul_assoc x y (x ^ m)]
        _ = c ^ m * ((c * (y * x)) * x ^ m) := by rw [hxy]
        _ = c ^ (m + 1) * (y * x ^ (m + 1)) := by
          rw [pow_succ, pow_succ']
          simp only [mul_assoc]
  have hB : ∀ m n : ℕ, x ^ m * y ^ n = c ^ (m * n) * (y ^ n * x ^ m) := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ m * y ^ (n + 1) = (x ^ m * y ^ n) * y := by rw [pow_succ, ← mul_assoc]
        _ = c ^ (m * n) * (y ^ n * (x ^ m * y)) := by rw [ih]; simp only [mul_assoc]
        _ = c ^ (m * n) * (y ^ n * (c ^ m * (y * x ^ m))) := by rw [hA m]
        _ = c ^ (m * n) * (c ^ m * (y ^ n * (y * x ^ m))) := by
          rw [← mul_assoc (y ^ n) (c ^ m), hcm (y ^ n) m, mul_assoc (c ^ m) (y ^ n)]
        _ = c ^ (m * (n + 1)) * (y ^ (n + 1) * x ^ m) := by
          rw [Nat.mul_succ, pow_add, pow_succ]
          simp only [mul_assoc]
  have hpow : ⁅x ^ a, y ^ a⁆ = c ^ (a ^ 2) := by
    rw [commutatorElement_def, hB a a, sq]
    calc c ^ (a * a) * (y ^ a * x ^ a) * (x ^ a)⁻¹ * (y ^ a)⁻¹
        = c ^ (a * a) * (y ^ a * x ^ a * (x ^ a)⁻¹ * (y ^ a)⁻¹) := by group
      _ = c ^ (a * a) := by group
  have drop1 : ∀ (w u z : Y), z ∈ Subgroup.center Y → ⁅w * z, u⁆ = ⁅w, u⁆ := by
    intro w u z hz
    have hzu : u * z = z * u := Subgroup.mem_center_iff.mp hz u
    have hzuz : z * u * z⁻¹ = u := by rw [← hzu]; group
    rw [commutatorElement_def, commutatorElement_def]
    calc w * z * u * (w * z)⁻¹ * u⁻¹ = w * (z * u * z⁻¹) * w⁻¹ * u⁻¹ := by group
      _ = w * u * w⁻¹ * u⁻¹ := by rw [hzuz]
  have drop2 : ∀ (w u z : Y), z ∈ Subgroup.center Y → ⁅w, u * z⁆ = ⁅w, u⁆ := by
    intro w u z hz
    calc ⁅w, u * z⁆ = ⁅u * z, w⁆⁻¹ := by rw [commutatorElement_inv]
      _ = ⁅u, w⁆⁻¹ := by rw [drop1 u w z hz]
      _ = ⁅w, u⁆ := by rw [commutatorElement_inv]
  have h1 : g * c * g⁻¹ = c := by rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
  have hgc : g * c * g⁻¹ = ⁅x ^ a * z₁, y ^ a * z₂⁆ := by
    have h := map_commutatorElement (MulAut.conj g) x y
    simp only [MulAut.conj_apply] at h
    rw [hx, hy] at h
    exact h
  have h2 : ⁅x ^ a * z₁, y ^ a * z₂⁆ = c ^ (a ^ 2) := by
    rw [drop1 _ _ _ hz₁, drop2 _ _ _ hz₂, hpow]
  have hc_eq : c = c ^ (a ^ 2) := by
    rw [← h2, ← hgc, h1]
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hpos : a ^ 2 = (a ^ 2 - 1) + 1 := by
    have : 0 < a ^ 2 := by positivity
    omega
  have hc1 : c ^ (a ^ 2 - 1) = 1 := by
    have h3 : c ^ (a ^ 2 - 1) * c = 1 * c := by
      rw [one_mul, ← pow_succ, ← hpos]
      exact hc_eq.symm
    exact mul_right_cancel h3
  have hcop : Nat.Coprime p (a ^ 2 - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr ha
  have hg1 : c ^ Nat.gcd p (a ^ 2 - 1) = 1 := pow_gcd_eq_one.mpr ⟨hpc, hc1⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg1
  exact hg1

end CFSG.HardMathSupport.Solomon.Proving

end
