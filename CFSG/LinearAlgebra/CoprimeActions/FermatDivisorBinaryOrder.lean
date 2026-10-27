module


public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LinearAlgebra.CoprimeActions.FermatDivisorBinaryOrder

theorem order_eq {k q : ℕ} (hk : 1 ≤ k) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ (2 ^ (k - 1)) + 1) :
    orderOf (2 : ZMod q) = 2 ^ k := by
  have odd_of_dvd {k q : ℕ} (hq : q.Prime) (hdvd : q ∣ 2 ^ (2 ^ (k - 1)) + 1) :
      Odd q := by
    rcases hq.eq_two_or_odd' with rfl | h
    · exfalso
      have : Even (2 ^ (2 ^ (k - 1)) + 1) := (even_iff_two_dvd).2 hdvd
      have h2 : Even (2 ^ (2 ^ (k - 1))) := (Nat.even_pow.2 ⟨even_two, by positivity⟩)
      exact (Nat.not_even_iff_odd.2 (h2.add_one)) this
    · exact h
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := odd_of_dvd (k := k) hq hdvd
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hdvd
  have h0 : ((2 : ZMod q) ^ (2 ^ m) + 1) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ q).2 hdvd
    simpa using this
  have hneg : (2 : ZMod q) ^ (2 ^ m) = -1 := eq_neg_of_add_eq_zero_left h0
  apply orderOf_eq_prime_pow
  · rw [hneg]
    intro h
    have h2 : (2 : ZMod q) = 0 := by
      have h' : (1 : ZMod q) + 1 = 0 := by
        calc (1 : ZMod q) + 1 = -1 + 1 := by rw [h]
          _ = 0 := neg_add_cancel 1
      simpa [one_add_one_eq_two] using h'
    have : ((2 : ℕ) : ZMod q) = 0 := by simpa using h2
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this
    subst this
    exact (Nat.not_even_iff_odd.2 hodd) even_two
  · rw [pow_succ, pow_mul, hneg]; exact neg_one_sq

theorem exists_prime {k : ℕ} (hk : 1 ≤ k) :
    ∃ q : ℕ, q.Prime ∧ q ∣ 2 ^ (2 ^ (k - 1)) + 1 ∧ Odd q ∧
      orderOf (2 : ZMod q) = 2 ^ k := by
  have odd_of_dvd {k q : ℕ} (hq : q.Prime) (hdvd : q ∣ 2 ^ (2 ^ (k - 1)) + 1) :
      Odd q := by
    rcases hq.eq_two_or_odd' with rfl | h
    · exfalso
      have : Even (2 ^ (2 ^ (k - 1)) + 1) := (even_iff_two_dvd).2 hdvd
      have h2 : Even (2 ^ (2 ^ (k - 1))) := (Nat.even_pow.2 ⟨even_two, by positivity⟩)
      exact (Nat.not_even_iff_odd.2 (h2.add_one)) this
    · exact h
  have h1 : 2 ^ (2 ^ (k - 1)) + 1 ≠ 1 := by
    have : 0 < 2 ^ (2 ^ (k - 1)) := by positivity
    omega
  obtain ⟨q, hq, hd⟩ := Nat.exists_prime_and_dvd h1
  exact ⟨q, hq, hd, odd_of_dvd hq hd, order_eq hk hq hd⟩

end CFSG.LinearAlgebra.CoprimeActions.FermatDivisorBinaryOrder
