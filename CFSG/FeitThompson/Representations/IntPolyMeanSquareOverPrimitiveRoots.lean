module

public import CFSG.FeitThompson.Foundations.CyclotomicIntegerFactorization
import CFSG.FeitThompson.Foundations.FiniteAmGmUnweighted
import CFSG.FeitThompson.Foundations.CyclotomicValueProductNonzero
import Mathlib.Algebra.Order.Algebra

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

theorem aeval_pow_eq_zero_of_aeval_eq_zero {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) {A : ℤ[X]} (hA : aeval ζ A = 0) {a : ℕ} (ha : a.Coprime n) :
    aeval (ζ ^ a) A = 0 := by
  have h : aeval ζ (A.map (algebraMap ℤ ℚ)) = 0 := by rwa [aeval_map_algebraMap]
  rw [aeval_eq_zero_iff_cyclotomic_rat_dvd hn hζ] at h
  rw [← aeval_map_algebraMap (A := ℚ) (ζ ^ a),
    aeval_eq_zero_iff_cyclotomic_rat_dvd hn (hζ.pow_of_coprime a ha)]
  exact h

theorem sq_norm_aeval_pow_pos {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {A : ℤ[X]} (hA : aeval ζ A ≠ 0) {a : ℕ} (ha : a ∈ coprimeIndices n) :
    0 < ‖aeval (ζ ^ a) A‖ ^ 2 := by
  have := aeval_pow_ne_zero_of_aeval_ne_zero hn hζ hA (mem_coprimeIndices.1 ha).2.2
  positivity

theorem one_le_prod_sq_norm_aeval_pow {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {A : ℤ[X]} (hA : aeval ζ A ≠ 0) :
    (1 : ℝ) ≤ ∏ a ∈ coprimeIndices n, ‖aeval (ζ ^ a) A‖ ^ 2 := by
  obtain ⟨-, m, hm0, hmeq⟩ := exists_int_prod_aeval_pow_ne_zero hn hζ hA
  rw [Finset.prod_pow, ← norm_prod, hmeq, Complex.norm_intCast]
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm0
  nlinarith [abs_nonneg ((m : ℝ))]

theorem totient_le_sum_sq_norm_aeval_pow {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {A : ℤ[X]} (hA : aeval ζ A ≠ 0) :
    (n.totient : ℝ) ≤ ∑ a ∈ coprimeIndices n, ‖aeval (ζ ^ a) A‖ ^ 2 := by
  have hs : (coprimeIndices n).Nonempty := by
    rw [← Finset.card_pos, card_coprimeIndices]
    exact Nat.totient_pos.2 hn
  have h := card_le_sum_of_one_le_prod hs
    (fun a ha => (sq_norm_aeval_pow_pos hn hζ hA ha).le)
    (one_le_prod_sq_norm_aeval_pow hn hζ hA)
  rwa [card_coprimeIndices] at h

theorem totient_le_sum_sq_norm_aeval_pow_and_pos {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) {A : ℤ[X]} (hA : aeval ζ A ≠ 0) :
    (n.totient : ℝ) ≤ ∑ a ∈ coprimeIndices n, ‖aeval (ζ ^ a) A‖ ^ 2 ∧
      ∀ a ∈ coprimeIndices n, 0 < ‖aeval (ζ ^ a) A‖ ^ 2 :=
  ⟨totient_le_sum_sq_norm_aeval_pow hn hζ hA, fun _a ha => sq_norm_aeval_pow_pos hn hζ hA ha⟩

theorem totient_le_sum_normSq_aeval_pow {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {A : ℤ[X]} (hA : aeval ζ A ≠ 0) :
    (n.totient : ℝ) ≤ ∑ a ∈ coprimeIndices n, Complex.normSq (aeval (ζ ^ a) A) := by
  simpa [Complex.normSq_eq_norm_sq] using totient_le_sum_sq_norm_aeval_pow hn hζ hA

theorem one_le_sum_sq_norm_aeval_pow_div_totient {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) {A : ℤ[X]} (hA : aeval ζ A ≠ 0) :
    (1 : ℝ) ≤ (∑ a ∈ coprimeIndices n, ‖aeval (ζ ^ a) A‖ ^ 2) / n.totient := by
  have hpos : (0 : ℝ) < n.totient := Nat.cast_pos.2 (Nat.totient_pos.2 hn)
  rw [le_div_iff₀ hpos, one_mul]
  exact totient_le_sum_sq_norm_aeval_pow hn hζ hA

end CFSG.FeitThompson
