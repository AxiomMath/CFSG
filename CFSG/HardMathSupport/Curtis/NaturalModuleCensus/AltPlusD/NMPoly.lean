module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open Polynomial

section Char2

variable {K : Type} [Field K] [CharP K 2]

theorem NM_two_eq_zero : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2

theorem NM_two_eq_zero_poly : (2 : K[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero K[X] 2

variable {V : Type} [AddCommGroup V] [Module K V]

theorem NM_two_smul_zero (y : V) : (2 : K) • y = 0 := by rw [NM_two_eq_zero, zero_smul]

theorem NM_add_self (K : Type) [Field K] [CharP K 2] [Module K V] (y : V) : y + y = 0 := by
  rw [← two_smul K y, NM_two_eq_zero, zero_smul]

theorem NM_eq_of_add_eq_zero (K : Type) [Field K] [CharP K 2] [Module K V] {x y : V} (h : x + y = 0) : x = y :=
  add_right_cancel (h.trans (NM_add_self K y).symm)

end Char2

section Root

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem NM_exists_root (hK : Nat.card K = 4) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  classical
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset K)) (t := Finset.univ)
    (by rw [Finset.card_univ, hcard]; exact lt_of_le_of_lt (Finset.card_le_two) (by norm_num))
  have h0 : ω ≠ 0 := fun h => hω (by simp [h])
  have h1 : ω ≠ 1 := fun h => hω (by simp [h])
  have h4 : ω ^ 4 = ω := by simpa [hcard] using FiniteField.pow_card ω
  have h2 : (2 : K) = 0 := NM_two_eq_zero
  have h3 : ω ^ 3 = 1 := by
    have : ω * (ω ^ 3 - 1) = 0 := by linear_combination h4
    have := (mul_eq_zero.mp this).resolve_left h0
    linear_combination this
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact ⟨ω, (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)⟩

end Root

section Eval

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (T : V →ₗ[K] V)

omit [CharP K 2] in
theorem NM_ev_mul (p q : K[X]) (v : V) :
    aeval T (p * q) v = aeval T p (aeval T q v) := by
  rw [map_mul]; rfl

theorem NM_ev_congr (hT5 : T ^ 5 = 1) {p q r : K[X]} (h : p = q + r * (X ^ 5 + 1)) (v : V) :
    aeval T p v = aeval T q v := by
  subst h
  rw [map_add, LinearMap.add_apply, NM_ev_mul]
  have : aeval T (X ^ 5 + 1 : K[X]) v = 0 := by
    simp [hT5, NM_add_self K]
  rw [this, map_zero, add_zero]

omit [CharP K 2] in
theorem NM_pow_mem {W : Submodule K V} (hW : ∀ w ∈ W, T w ∈ W) (n : ℕ) :
    ∀ w ∈ W, (T ^ n) w ∈ W := by
  induction n with
  | zero => intro w hw; simpa using hw
  | succ n ih =>
    intro w hw
    rw [pow_succ', Module.End.mul_apply]
    exact hW _ (ih w hw)

omit [CharP K 2] in
theorem NM_ev_mem {W : Submodule K V} (hW : ∀ w ∈ W, T w ∈ W) (p : K[X]) :
    ∀ w ∈ W, aeval T p w ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro w hw
    rw [map_add, LinearMap.add_apply]
    exact add_mem (hp w hw) (hq w hw)
  | monomial n c =>
    intro w hw
    rw [← C_mul_X_pow_eq_monomial, map_mul, aeval_C, aeval_X_pow]
    simp only [Module.algebraMap_end_apply, Module.End.mul_apply]
    exact W.smul_mem _ (NM_pow_mem T hW n w hw)

theorem NM_quad_of_ev {a : K} {f : V} (h : aeval T (X ^ 2 + C a * X + 1 : K[X]) f = 0) :
    T (T f) = a • T f + f := by
  simp [pow_two] at h
  linear_combination (norm := module) h - NM_two_smul_zero (K := K) (a • T f + f)

end Eval

section Vec

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (T : V →ₗ[K] V)

theorem NM_exists_quadratic_vec (hK : Nat.card K = 4) (hT5 : T ^ 5 = 1) (W : Submodule K V)
    (hW : ∀ w ∈ W, T w ∈ W) {f : V} (hfW : f ∈ W) (hf : T f ≠ f) :
    ∃ (a : K) (f' : V), a ^ 2 + a + 1 = 0 ∧ f' ∈ W ∧ f' ≠ 0 ∧ T (T f') = a • T f' + f' := by
  obtain ⟨ω, hω⟩ := NM_exists_root hK
  have h2 : (2 : K[X]) = 0 := NM_two_eq_zero_poly
  have h2K : (2 : K) = 0 := NM_two_eq_zero
  have hω' : (C ω) ^ 2 + C ω + 1 = (0 : K[X]) := by
    rw [← C_pow, ← C_1, ← C_add, ← C_add, hω, C_0]
  have hC : (C (ω + 1) : K[X]) = C ω + 1 := by simp
  set Φ5 : K[X] := 1 + X + X ^ 2 + X ^ 3 + X ^ 4 with hΦ5
  have pI1 : Φ5 = (X ^ 2 + C ω * X + 1) * (X ^ 2 + C (ω + 1) * X + 1) + 0 * (X ^ 5 + 1) := by
    rw [hC]
    linear_combination (-X ^ 2 : K[X]) * hω' + (-(C ω) * (X ^ 3 + X) : K[X]) * h2
  have pI2 : Φ5 * (1 + Φ5) = 0 + (X * (1 + X) ^ 2) * (X ^ 5 + 1) := by
    rw [hΦ5]
    linear_combination (1 + X + X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + X ^ 6 : K[X]) * h2
  have pI3 : X + 1 = (X + 1) * (1 + Φ5) + 1 * (X ^ 5 + 1) := by
    rw [hΦ5]
    linear_combination (-(1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5) : K[X]) * h2
  have hmem := NM_ev_mem T hW
  set f2 : V := aeval T (1 + Φ5) f with hf2
  have hf2W : f2 ∈ W := hmem _ f hfW
  have hΦf2 : aeval T Φ5 f2 = 0 := by
    rw [hf2, ← NM_ev_mul, NM_ev_congr T hT5 pI2]
    simp
  have hf2ne : f2 ≠ 0 := by
    intro h0
    apply hf
    have h1 : aeval T (X + 1 : K[X]) f = 0 := by
      rw [NM_ev_congr T hT5 pI3, NM_ev_mul, ← hf2, h0, map_zero]
    simp only [map_add, aeval_X, map_one, LinearMap.add_apply, Module.End.one_apply] at h1
    exact NM_eq_of_add_eq_zero K h1
  have hP12 : aeval T ((X ^ 2 + C ω * X + 1) * (X ^ 2 + C (ω + 1) * X + 1)) f2 = 0 :=
    (NM_ev_congr T hT5 pI1 f2).symm.trans hΦf2
  by_cases h : aeval T (X ^ 2 + C (ω + 1) * X + 1 : K[X]) f2 = 0
  · refine ⟨ω + 1, f2, ?_, hf2W, hf2ne, NM_quad_of_ev T h⟩
    linear_combination hω + (ω + 1) * h2K
  · refine ⟨ω, aeval T (X ^ 2 + C (ω + 1) * X + 1 : K[X]) f2, hω, hmem _ f2 hf2W, h,
      NM_quad_of_ev T ?_⟩
    rw [← NM_ev_mul]
    exact hP12

end Vec

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
