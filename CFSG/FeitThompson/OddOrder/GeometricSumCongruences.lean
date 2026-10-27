module

public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.FieldTheory.Finite.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

theorem sum_range_pow_mul_sub_one {p : ℕ} (hp : 1 ≤ p) (q : ℕ) :
    (∑ i ∈ range q, p ^ i) * (p - 1) + 1 = p ^ q := by
  obtain ⟨x, rfl⟩ : ∃ x, p = x + 1 := ⟨p - 1, by omega⟩
  simpa using geom_sum_mul_add x q

theorem sum_range_pow_eq_div {p : ℕ} (hp : 2 ≤ p) (q : ℕ) :
    ∑ i ∈ range q, p ^ i = (p ^ q - 1) / (p - 1) := by
  have h := sum_range_pow_mul_sub_one (p := p) (by omega) q
  have h2 : p ^ q - 1 = (∑ i ∈ range q, p ^ i) * (p - 1) := by omega
  rw [h2, Nat.mul_div_cancel _ (by omega)]

theorem sum_range_pow_modEq_one {p q : ℕ} (hq : 0 < q) :
    (∑ i ∈ range q, p ^ i) ≡ 1 [MOD p] := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simpa using
    (Nat.modEq_zero_iff_dvd.2
      (Finset.dvd_sum fun i _ => dvd_pow_self p (Nat.succ_ne_zero i))).add_right 1

theorem sum_range_pow_modEq_card {p q m : ℕ} (h : p ≡ 1 [MOD m]) :
    (∑ i ∈ range q, p ^ i) ≡ q [MOD m] := by
  calc (∑ i ∈ range q, p ^ i) ≡ ∑ _i ∈ range q, 1 [MOD m] :=
        Nat.ModEq.sum fun i _ => by simpa using h.pow i
    _ = q := by simp

theorem gcd_sum_range_pow_sub_one {p : ℕ} (hp : 1 ≤ p) (q : ℕ) :
    Nat.gcd (∑ i ∈ range q, p ^ i) (p - 1) = Nat.gcd q (p - 1) :=
  Nat.ModEq.gcd_eq (sum_range_pow_modEq_card ((Nat.modEq_iff_dvd' hp).2 dvd_rfl).symm)

theorem sum_range_pow_modEq_zero {p q : ℕ} (h : p ≡ 1 [MOD q]) :
    (∑ i ∈ range q, p ^ i) ≡ 0 [MOD q] :=
  (sum_range_pow_modEq_card h).trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)

theorem sum_range_pow_modEq_one_of_not_modEq {p q : ℕ} (hq : q.Prime)
    (h : ¬ p ≡ 1 [MOD q]) : (∑ i ∈ range q, p ^ i) ≡ 1 [MOD q] := by
  have := Fact.mk hq
  have hx : (p : ZMod q) - 1 ≠ 0 := by
    intro hx
    exact h ((ZMod.natCast_eq_natCast_iff _ _ _).1 (by push_cast; linear_combination hx))
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  have hgs := geom_sum_mul (x := (p : ZMod q)) q
  rw [ZMod.pow_card] at hgs
  refine mul_right_cancel₀ hx ?_
  rw [hgs]
  ring

theorem sum_range_pow_congruences {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (∑ i ∈ range q, p ^ i) = (p ^ q - 1) / (p - 1) ∧
      (∑ i ∈ range q, p ^ i) ≡ 1 [MOD p] ∧
      Nat.gcd (∑ i ∈ range q, p ^ i) (p - 1) = Nat.gcd q (p - 1) ∧
      (p ≡ 1 [MOD q] → (∑ i ∈ range q, p ^ i) ≡ 0 [MOD q]) ∧
      (¬ p ≡ 1 [MOD q] → (∑ i ∈ range q, p ^ i) ≡ 1 [MOD q]) :=
  ⟨sum_range_pow_eq_div hp.two_le q, sum_range_pow_modEq_one hq.pos,
    gcd_sum_range_pow_sub_one hp.one_lt.le q, sum_range_pow_modEq_zero,
    sum_range_pow_modEq_one_of_not_modEq hq⟩

end CFSG.FeitThompson
