module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.CGT.Stroth77.Stroth34Arith

theorem isCoprime_two_pow_of_odd {a : ℤ} (ha : Odd a) (j : ℕ) : IsCoprime ((2 : ℤ) ^ j) a := by
  apply IsCoprime.pow_left
  rw [Int.isCoprime_iff_gcd_eq_one]
  obtain ⟨b, rfl⟩ := ha
  have : Int.gcd 2 (2 * b + 1) = Int.gcd 2 1 := by
    rw [show (2 * b + 1 : ℤ) = 1 + 2 * b by ring, Int.gcd_add_mul_left_right]
  rw [this]
  rfl

theorem sq_cases {j : ℕ} {y : ℤ} (h : (2 : ℤ) ^ (j + 2) ∣ y ^ 2 - 1) :
    (2 : ℤ) ^ (j + 1) ∣ y - 1 ∨ (2 : ℤ) ^ (j + 1) ∣ y + 1 := by
  have hy : Odd y := by
    rcases Int.even_or_odd y with ⟨b, rfl⟩ | hodd
    · exfalso
      have h4 : (4 : ℤ) ∣ (b + b) ^ 2 - 1 :=
        dvd_trans (by rw [pow_add]; exact dvd_mul_left _ _) h
      have : (b + b) ^ 2 - 1 = 4 * (b * b) - 1 := by ring
      rw [this] at h4
      omega
    · exact hodd
  obtain ⟨a, rfl⟩ := hy
  have e1 : (2 * a + 1) ^ 2 - 1 = 2 ^ 2 * (a * (a + 1)) := by ring
  rw [e1, pow_add] at h
  have h' : (2 : ℤ) ^ j ∣ a * (a + 1) :=
    (mul_dvd_mul_iff_right (by positivity : (2 : ℤ) ^ 2 ≠ 0)).mp (by simpa [mul_comm] using h)
  rcases Int.even_or_odd a with ha | ha
  ·
    have hco := isCoprime_two_pow_of_odd (ha.add_one) j
    have := hco.dvd_of_dvd_mul_right h'
    left
    rw [show 2 * a + 1 - 1 = 2 * a by ring, pow_succ']
    exact mul_dvd_mul_left 2 this
  · have hco := isCoprime_two_pow_of_odd ha j
    have := hco.dvd_of_dvd_mul_left h'
    right
    rw [show 2 * a + 1 + 1 = 2 * (a + 1) by ring, pow_succ']
    exact mul_dvd_mul_left 2 this

theorem sq_cases' {j : ℕ} {y : ℤ} (h : (2 : ℤ) ^ (j + 2) ∣ y ^ 2 - 1) :
    (2 : ℤ) ^ (j + 2) ∣ y - 1 ∨ (2 : ℤ) ^ (j + 2) ∣ y + 1 ∨
      (2 : ℤ) ^ (j + 2) ∣ y - (1 + 2 ^ (j + 1)) ∨ (2 : ℤ) ^ (j + 2) ∣ y - (-1 + 2 ^ (j + 1)) := by
  have hp : (2 : ℤ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
  rcases sq_cases h with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases Int.even_or_odd k with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · left; exact ⟨l, by rw [hp]; linear_combination hk⟩
    · right; right; left; exact ⟨l, by rw [hp]; linear_combination hk⟩
  · rcases Int.even_or_odd k with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · right; left; exact ⟨l, by rw [hp]; linear_combination hk⟩
    · right; right; right; exact ⟨l, by rw [hp]; linear_combination hk⟩

theorem sq_odd_mod_eight {y : ℤ} (hy : Odd y) : (8 : ℤ) ∣ y ^ 2 - 1 := by
  obtain ⟨a, rfl⟩ := hy
  have e1 : (2 * a + 1) ^ 2 - 1 = 4 * (a * (a + 1)) := by ring
  rw [e1]
  have : (2 : ℤ) ∣ a * (a + 1) := by
    rcases Int.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨b * (b + b + 1), by ring⟩
    · exact ⟨(2 * b + 1) * (b + 1), by ring⟩
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by rw [hc]; ring⟩

theorem sq_eq_one_add_cases {j : ℕ} (hj : 1 ≤ j) {y : ℤ} (hy4 : (4 : ℤ) ∣ y - 1)
    (h : (2 : ℤ) ^ (j + 2) ∣ y ^ 2 - (1 + 2 ^ (j + 1))) :
    (2 : ℤ) ^ (j + 1) ∣ y - (1 + 2 ^ j) := by
  obtain ⟨a, ha⟩ := hy4
  have e1 : y ^ 2 - (1 + 2 ^ (j + 1)) = 2 * (4 * a * (2 * a + 1) - 2 ^ j) := by
    rw [show y = 4 * a + 1 by linear_combination ha]; ring
  rw [e1, pow_succ'] at h
  have h' : (2 : ℤ) ^ (j + 1) ∣ 4 * a * (2 * a + 1) - 2 ^ j :=
    (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
  have hco := isCoprime_two_pow_of_odd (⟨a, rfl⟩ : Odd (2 * a + 1)) (j + 1)
  have key : (2 : ℤ) ^ (j + 1) ∣ (4 * a - 2 ^ j) * (2 * a + 1) := by
    have : (4 * a - 2 ^ j) * (2 * a + 1) = (4 * a * (2 * a + 1) - 2 ^ j) - 2 ^ j * (2 * a) := by
      ring
    rw [this]
    refine dvd_sub h' ?_
    rw [pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right 2 a)
  have := hco.dvd_of_dvd_mul_right key
  rw [show y - (1 + 2 ^ j) = 4 * a - 2 ^ j by linear_combination ha]
  exact this

end CFSG.CGT.Stroth77.Stroth34Arith
