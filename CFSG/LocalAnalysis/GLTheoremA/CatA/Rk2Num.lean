module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Num

variable {p n : ℕ}

private theorem natCast_pow_sub_one (a : ℕ) : (((2 ^ a - 1 : ℕ)) : ZMod p) = (2 : ZMod p) ^ a - 1 := by
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  rfl

theorem rk2Ord_dvd_iff (k : ℕ) : rk2Ord p n ∣ k ↔ p ∣ 2 ^ (n * k) - 1 := by
  unfold rk2Ord
  rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← ZMod.natCast_eq_zero_iff, natCast_pow_sub_one, sub_eq_zero]

theorem rk2Ord_pos (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) : 0 < rk2Ord p n := by
  have hF : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  unfold rk2Ord
  refine orderOf_pos_iff.2 ?_
  rw [isOfFinOrder_iff_pow_eq_one]
  exact ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one (pow_ne_zero n h2)⟩

private theorem prime_not_dvd_both (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    ¬ (p ∣ 2 ^ n - 1 ∧ p ∣ 2 ^ n + 1) := by
  rintro ⟨h1, h2⟩
  have h3 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
  have h4 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

private theorem two_pow_mul_two_sub_one (n : ℕ) : 2 ^ (n * 2) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  have h1 := Nat.one_le_two_pow (n := n)
  have : 2 ^ (n * 2) = 2 ^ n * 2 ^ n := by rw [pow_mul, sq]
  rw [this]
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ n = a + 1 := ⟨2 ^ n - 1, by omega⟩
  rw [ha]
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

theorem rk2Ord_eq_one_iff : rk2Ord p n = 1 ↔ p ∣ 2 ^ n - 1 := by
  rw [← Nat.dvd_one, rk2Ord_dvd_iff, mul_one]

theorem rk2Ord_eq_two_iff (hp : p.Prime) (hp2 : p ≠ 2) : rk2Ord p n = 2 ↔ p ∣ 2 ^ n + 1 := by
  have hpos := rk2Ord_pos hp hp2 n
  have hdvd : rk2Ord p n ∣ 2 ↔ p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [rk2Ord_dvd_iff, two_pow_mul_two_sub_one]
  constructor
  · intro h
    have h' := hdvd.1 (h ▸ dvd_refl _)
    rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h1
    · exact absurd (rk2Ord_eq_one_iff.2 h1) (by omega)
    · exact h1
  · intro h
    have h' : rk2Ord p n ∣ 2 := hdvd.2 (dvd_mul_of_dvd_right h _)
    rcases (Nat.dvd_prime Nat.prime_two).1 h' with h1 | h1
    · exact absurd (rk2Ord_eq_one_iff.1 h1) (fun h2 => prime_not_dvd_both hp hp2 n ⟨h2, h⟩)
    · exact h1

theorem rk2Ord_one_eq_two_iff (hp : p.Prime) (hp2 : p ≠ 2) : rk2Ord p 1 = 2 ↔ p = 3 := by
  rw [rk2Ord_eq_two_iff hp hp2]
  constructor
  · intro h
    have h' : p ∣ 3 := by simpa using h
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h'
  · rintro rfl
    norm_num

theorem rk2Ord_one_ne_one (hp : p.Prime) : rk2Ord p 1 ≠ 1 := by
  rw [Ne, rk2Ord_eq_one_iff]
  simpa using hp.one_lt.ne'

theorem rk2Ord_one_eq_three_iff (hp : p.Prime) : rk2Ord p 1 = 3 ↔ p = 7 := by
  constructor
  · intro h
    have h' : rk2Ord p 1 ∣ 3 := h ▸ dvd_refl _
    rw [rk2Ord_dvd_iff] at h'
    have h7 : p ∣ 7 := by simpa using h'
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7
  · rintro rfl
    have h3 : rk2Ord 7 1 ∣ 3 := by
      rw [rk2Ord_dvd_iff]
      norm_num
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact absurd h (rk2Ord_one_ne_one (by norm_num))
    · exact h

end Num

end CFSG.LocalAnalysis.GLTheoremA
