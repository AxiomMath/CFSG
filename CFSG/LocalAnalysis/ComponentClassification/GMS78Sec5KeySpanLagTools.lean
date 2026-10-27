module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.GMS78.VLike

open Polynomial

theorem range_eq_ker_of_ker_le_range {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (M : V × V →ₗ[F] V) (Z : V →ₗ[F] V × V)
    (h : LinearMap.ker M ≤ LinearMap.range Z) :
    LinearMap.range Z = LinearMap.ker M ∧ LinearMap.ker Z = ⊥ := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M
  have h2 := LinearMap.finrank_range_add_finrank_ker Z
  have h3 : Module.finrank F (V × V) = Module.finrank F V + Module.finrank F V :=
    Module.finrank_prod
  have h4 : Module.finrank F (LinearMap.range M) ≤ Module.finrank F V := Submodule.finrank_le _
  have h5 := Submodule.finrank_mono h
  refine ⟨(Submodule.eq_of_le_of_finrank_le h (by omega)).symm, ?_⟩
  exact Submodule.finrank_eq_zero.mp (by omega)

variable {K : Type*} [Field K] [Fintype K]

theorem coeffs_eq_zero_of_vanish_five {a : ℕ} (ha : 2 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {α₀ α₁ α₂ α₃ α₄ : K}
    (h : ∀ δ : K, α₀ * δ ^ 2 ^ (2 * a) + α₁ * δ ^ 2 ^ a + α₂ * δ + α₃ * δ ^ 2 ^ (a + 1) +
      α₄ * δ ^ 2 = 0) : α₃ = 0 ∧ α₄ = 0 := by
  classical
  set p : K[X] := C α₀ * X ^ 2 ^ (2 * a) + C α₁ * X ^ 2 ^ a + C α₂ * X +
    C α₃ * X ^ 2 ^ (a + 1) + C α₄ * X ^ 2 with hp
  have e1 : 2 ^ a < 2 ^ (2 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e2 : 2 ^ (a + 1) < 2 ^ (2 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e3 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have e4 : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e5 : 2 ^ (2 * a) < 2 ^ (2 * a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hdeg : p.natDegree ≤ 2 ^ (2 * a) := by
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_) ?_
    · exact natDegree_C_mul_X_pow_le _ _
    · exact (natDegree_C_mul_X_pow_le _ _).trans e1.le
    · exact (natDegree_C_mul_le _ X).trans (natDegree_X_le.trans (by omega))
    · exact (natDegree_C_mul_X_pow_le _ _).trans e2.le
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have hp0 : p = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Finset.univ (fun z _ => ?_) ?_
    · simpa [hp] using h z
    · rw [Finset.card_univ, hK]; omega
  have c3 := congrArg (fun r : K[X] => r.coeff (2 ^ (a + 1))) hp0
  have c4 := congrArg (fun r : K[X] => r.coeff 2) hp0
  have n1 : (2 ^ (2 * a) : ℕ) ≠ 2 ^ (a + 1) := e2.ne'
  have n2 : (2 ^ a : ℕ) ≠ 2 ^ (a + 1) := e4.ne
  have n3 : (1 : ℕ) ≠ 2 ^ (a + 1) := by have := Nat.one_lt_two_pow (n := a + 1) (by omega); omega
  have n4 : (2 : ℕ) ≠ 2 ^ (a + 1) := by
    have : 2 ^ 2 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have m1 : (2 ^ (2 * a) : ℕ) ≠ 2 := by omega
  have m2 : (2 ^ a : ℕ) ≠ 2 := by omega
  have m3 : (2 ^ (a + 1) : ℕ) ≠ 2 := n4.symm
  simp only [hp, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_zero] at c3 c4
  have k1 : a + 1 ≠ 2 * a := by omega
  refine ⟨?_, ?_⟩
  · simpa [n1, n2, n3, n4.symm, k1] using c3
  · simpa [m1.symm, m2.symm, m3.symm] using c4


section Algebra

variable {K : Type*} [Field K] (φ ψ : K →+* K)

theorem lag_inv [CharP K 2] (hψφ : ∀ y, ψ (φ y) = y)
    {u r s c β C A₀ A₁ Rm R0 R1 R2 δ w₁ w₂ : K} (hC : C ≠ 0)
    (hA₀ : A₀ = s / C) (hA₁ : A₁ = φ c * u / C) (hRm : Rm = (ψ u + ψ β * ψ A₀) / C)
    (hR0 : R0 = (φ u + ψ β * ψ A₁) / C) (hR1 : R1 = (φ c * r + β * φ A₀) / C)
    (hR2 : R2 = β * φ A₁ / C) (h1 : C * w₁ = φ c * u * φ δ + s * δ)
    (h2 : ψ (β * w₁) + β * φ w₁ + C * w₂ = ψ (δ * u) + φ u * δ + φ c * r * φ δ) :
    w₁ = A₀ * δ + A₁ * φ δ ∧ w₂ = Rm * ψ δ + R0 * δ + R1 * φ δ + R2 * φ (φ δ) := by
  have hw₁ : w₁ = A₀ * δ + A₁ * φ δ := by
    rw [hA₀, hA₁]
    field_simp
    linear_combination h1
  refine ⟨hw₁, ?_⟩
  have h3 : C * w₂ = ψ (δ * u) + φ u * δ + φ c * r * φ δ + (ψ (β * w₁) + β * φ w₁) := by
    linear_combination h2 - (ψ (β * w₁) + β * φ w₁) * (CharTwo.two_eq_zero : (2 : K) = 0)
  rw [hw₁] at h3
  simp only [map_add, map_mul, hψφ] at h3
  rw [hRm, hR0, hR1, hR2]
  field_simp
  linear_combination h3

theorem lag_expand (hψφ : ∀ y, ψ (φ y) = y)
    {u r s c A₀ A₁ Rm R0 R1 R2 Pmm Pm P0 P1 P2 : K} (δ : K)
    (hPmm : Pmm = c * ψ u * ψ Rm) (hPm : Pm = c * ψ u * ψ R0 + c * ψ r * ψ A₀ + s * Rm)
    (hP0 : P0 = φ u * A₀ + c * ψ u * ψ R1 + c * ψ r * ψ A₁ + s * R0)
    (hP1 : P1 = u * φ A₀ + φ u * A₁ + c * ψ u * ψ R2 + s * R1)
    (hP2 : P2 = u * φ A₁ + s * R2) :
    u * φ (A₀ * δ + A₁ * φ δ) + φ u * (A₀ * δ + A₁ * φ δ) +
        c * (ψ (u * (Rm * ψ δ + R0 * δ + R1 * φ δ + R2 * φ (φ δ))) +
          ψ ((A₀ * δ + A₁ * φ δ) * r)) +
        s * (Rm * ψ δ + R0 * δ + R1 * φ δ + R2 * φ (φ δ)) =
      Pmm * ψ (ψ δ) + Pm * ψ δ + P0 * δ + P1 * φ δ + P2 * φ (φ δ) := by
  simp only [map_add, map_mul, hψφ]
  rw [hPmm, hPm, hP0, hP1, hP2]
  ring

theorem lag_final [CharP K 2] (hψφ : ∀ y, ψ (φ y) = y)
    {u r s c β C A₀ A₁ R1 R2 P1 P2 : K} (hu : u ≠ 0) (hc : c ≠ 0) (hβ : β ≠ 0)
    (hCdef : C = φ (β * c)) (hA₁ : A₁ = φ c * u / C)
    (hR1 : R1 = (φ c * r + β * φ A₀) / C) (hR2 : R2 = β * φ A₁ / C)
    (hP1 : P1 = u * φ A₀ + φ u * A₁ + c * ψ u * ψ R2 + s * R1)
    (hP2 : P2 = u * φ A₁ + s * R2) (h1 : P1 = 0) (h2 : P2 = 0) :
    φ c * u * φ β + s * β = 0 ∧ ψ (β * u) + φ u * β + φ c * r * φ β = 0 := by
  have hφβ : φ β ≠ 0 := (map_ne_zero φ).mpr hβ
  have hφc : φ c ≠ 0 := (map_ne_zero φ).mpr hc
  have hC : C ≠ 0 := by rw [hCdef, map_mul]; exact mul_ne_zero hφβ hφc
  have hCm : C = φ β * φ c := by rw [hCdef, map_mul]
  have hA₁' : A₁ = u / φ β := by rw [hA₁, hCm]; field_simp
  have hφA₁ : φ A₁ ≠ 0 := (map_ne_zero φ).mpr (by rw [hA₁']; exact div_ne_zero hu hφβ)
  have hrel : u * C + s * β = 0 := by
    have h : φ A₁ * (u * C + s * β) = 0 := by
      have : P2 * C = φ A₁ * (u * C + s * β) := by rw [hP2, hR2]; field_simp
      rw [← this, h2, zero_mul]
    exact (mul_eq_zero.mp h).resolve_left hφA₁
  refine ⟨by rw [← hrel, hCm]; ring, ?_⟩
  have hψR2 : ψ R2 = ψ β * A₁ / (β * c) := by
    rw [hR2, map_div₀, map_mul, hψφ, hCdef, hψφ]
  have hsC : s / C = -(u / β) := by
    field_simp
    linear_combination hrel
  have hsR1 : s * R1 = -(u / β) * (φ c * r) + s * β * φ A₀ / C := by
    rw [hR1, ← hsC]; ring
  have hP1' : P1 = φ A₀ * (u * C + s * β) / C + φ u * A₁ + c * ψ u * ψ R2 -
      u / β * (φ c * r) := by
    rw [hP1, hsR1]; field_simp; ring
  rw [hrel, mul_zero, zero_div, zero_add, hψR2, hA₁'] at hP1'
  have h3 : u * (β * φ u + ψ β * ψ u - φ c * r * φ β) = 0 := by
    have : β * φ β * P1 = u * (β * φ u + ψ β * ψ u - φ c * r * φ β) := by
      rw [hP1']; field_simp
    rw [← this, h1, mul_zero]
  have h4 := (mul_eq_zero.mp h3).resolve_left hu
  rw [map_mul]
  linear_combination h4 + φ c * r * φ β * (CharTwo.two_eq_zero : (2 : K) = 0)

end Algebra

end CFSG.ComponentClassification.GMS78.VLike
