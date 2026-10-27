module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem odd_divisor_form {d : ℕ} (hd : d ∣ 2 ^ 17 * 3 ^ 2 * 7 * 23 * 29 * 31 * 37 * 43)
    (hodd : ¬ 2 ∣ d) :
    ∃ b ≤ 2, ∃ e7 e23 e29 e31 e37 e43 : ℕ,
      (e7 = 1 ∨ e7 = 7) ∧ (e23 = 1 ∨ e23 = 23) ∧ (e29 = 1 ∨ e29 = 29) ∧
      (e31 = 1 ∨ e31 = 31) ∧ (e37 = 1 ∨ e37 = 37) ∧ (e43 = 1 ∨ e43 = 43) ∧
      d = 3 ^ b * e7 * e23 * e29 * e31 * e37 * e43 := by
  obtain ⟨d1, e43, h1, h43, rfl⟩ := Nat.dvd_mul.mp hd
  obtain ⟨d2, e37, h2, h37, rfl⟩ := Nat.dvd_mul.mp h1
  obtain ⟨d3, e31, h3, h31, rfl⟩ := Nat.dvd_mul.mp h2
  obtain ⟨d4, e29, h4, h29, rfl⟩ := Nat.dvd_mul.mp h3
  obtain ⟨d5, e23, h5, h23, rfl⟩ := Nat.dvd_mul.mp h4
  obtain ⟨d6, e7, h6, h7, rfl⟩ := Nat.dvd_mul.mp h5
  obtain ⟨k2, k3, hk2, hk3, rfl⟩ := Nat.dvd_mul.mp h6
  obtain ⟨a, ha17, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk2
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hk3
  have ha : a = 0 := by
    by_contra ha
    have h2a : 2 ∣ 2 ^ a := dvd_pow_self 2 ha
    exact hodd (by repeat' apply dvd_mul_of_dvd_left
                   exact h2a)
  subst ha
  have h7' := (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h7
  have h23' := (Nat.dvd_prime (by norm_num : Nat.Prime 23)).mp h23
  have h29' := (Nat.dvd_prime (by norm_num : Nat.Prime 29)).mp h29
  have h31' := (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp h31
  have h37' := (Nat.dvd_prime (by norm_num : Nat.Prime 37)).mp h37
  have h43' := (Nat.dvd_prime (by norm_num : Nat.Prime 43)).mp h43
  exact ⟨b, hb, e7, e23, e29, e31, e37, e43, h7', h23', h29', h31', h37', h43', by simp⟩

theorem divisor_mod_1331_odd {d : ℕ} (hd : d ∣ 2 ^ 17 * 3 ^ 2 * 7 * 23 * 29 * 31 * 37 * 43)
    (hodd : ¬ 2 ∣ d) (h : d % 1331 = 1) : d = 1 := by
  obtain ⟨b, hb, e7, e23, e29, e31, e37, e43, h7, h23, h29, h31, h37, h43, rfl⟩ :=
    odd_divisor_form hd hodd
  interval_cases b <;> rcases h7 with rfl | rfl <;> rcases h23 with rfl | rfl <;>
    rcases h29 with rfl | rfl <;> rcases h31 with rfl | rfl <;> rcases h37 with rfl | rfl <;>
    rcases h43 with rfl | rfl <;> revert h <;> norm_num

theorem divisor_mod_1331_one_or_two_dvd {d : ℕ}
    (hd : d ∣ 2 ^ 17 * 3 ^ 2 * 7 * 23 * 29 * 31 * 37 * 43) (h : d % 1331 = 1) :
    d = 1 ∨ 2 ∣ d := by
  by_cases hodd : 2 ∣ d
  · exact Or.inr hodd
  · exact Or.inl (divisor_mod_1331_odd hd hodd h)

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
