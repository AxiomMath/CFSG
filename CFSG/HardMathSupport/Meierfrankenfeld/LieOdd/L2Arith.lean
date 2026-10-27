module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

private theorem pow_five_lt_two_pow_two_mul {n : ℕ} (hn : 9 ≤ n) : n ^ 5 < 2 ^ (2 * n) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h4 : 2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
      norm_num
      ring
    have hpoly : (n + 1) ^ 5 ≤ 4 * n ^ 5 := by
      nlinarith [pow_pos (show (0 : ℕ) < n by omega) 2, pow_pos (show (0 : ℕ) < n by omega) 3,
        pow_pos (show (0 : ℕ) < n by omega) 4]
    rw [h4]
    omega

private theorem five_lt_two_pow {j : ℕ} (hj : 25 ≤ j) : (j + 2) ^ 5 < 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    have hpoly : (j + 1 + 2) ^ 5 ≤ 2 * (j + 2) ^ 5 := by
      nlinarith [pow_pos (show (0 : ℕ) < j + 2 by omega) 2,
        pow_pos (show (0 : ℕ) < j + 2 by omega) 3, pow_pos (show (0 : ℕ) < j + 2 by omega) 4]
    rw [h2]
    omega

private theorem mul_three_le_sq {p f : ℕ} (hp : 3 ≤ p) :
    (f + 3) * p ^ 3 ≤ (p ^ (f + 2)) ^ 2 := by
  induction f with
  | zero =>
    have h := Nat.mul_le_mul_right (p ^ 3) hp
    calc (0 + 3) * p ^ 3 = 3 * p ^ 3 := by ring
      _ ≤ p * p ^ 3 := h
      _ = (p ^ (0 + 2)) ^ 2 := by ring
  | succ f ih =>
    have e1 : (p ^ (f + 1 + 2)) ^ 2 = p ^ 2 * (p ^ (f + 2)) ^ 2 := by ring
    have hp2 : 9 ≤ p ^ 2 := by nlinarith
    rw [e1]
    have h3 : (f + 3) * p ^ 3 * p ^ 2 ≤ (p ^ (f + 2)) ^ 2 * p ^ 2 := Nat.mul_le_mul_right _ ih
    have h4 : (f + 1 + 3) * p ^ 3 ≤ (f + 3) * p ^ 3 * p ^ 2 := by
      have := Nat.mul_le_mul_left ((f + 3) * p ^ 3) hp2
      nlinarith [this, Nat.zero_le (f * p ^ 3), Nat.zero_le (p ^ 3)]
    calc (f + 1 + 3) * p ^ 3 ≤ (f + 3) * p ^ 3 * p ^ 2 := h4
      _ ≤ (p ^ (f + 2)) ^ 2 * p ^ 2 := h3
      _ = p ^ 2 * (p ^ (f + 2)) ^ 2 := by ring

private theorem lhs_le_pow_five {p f : ℕ} (hp : 3 ≤ p) :
    p ^ (f + 3) * (p ^ (2 * (f + 3)) - 1) * (f + 3) ≤ (p ^ (f + 2)) ^ 5 := by
  have h1 : p ^ (f + 3) * (p ^ (2 * (f + 3)) - 1) ≤ p ^ (3 * (f + 3)) := by
    calc p ^ (f + 3) * (p ^ (2 * (f + 3)) - 1) ≤ p ^ (f + 3) * p ^ (2 * (f + 3)) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = p ^ (3 * (f + 3)) := by ring
  have h2 : p ^ (3 * (f + 3)) * (f + 3) = (p ^ (f + 2)) ^ 3 * ((f + 3) * p ^ 3) := by ring
  calc p ^ (f + 3) * (p ^ (2 * (f + 3)) - 1) * (f + 3) ≤ p ^ (3 * (f + 3)) * (f + 3) :=
        Nat.mul_le_mul_right _ h1
    _ = (p ^ (f + 2)) ^ 3 * ((f + 3) * p ^ 3) := h2
    _ ≤ (p ^ (f + 2)) ^ 3 * (p ^ (f + 2)) ^ 2 := Nat.mul_le_mul_left _ (mul_three_le_sq hp)
    _ = (p ^ (f + 2)) ^ 5 := by ring

private theorem le_div_of_mul {p m : ℕ} (hp : 3 ≤ p) (hm : 1 ≤ m) :
    m ≤ (p * m - 1) / (p - 1) := by
  apply (Nat.le_div_iff_mul_le (by omega)).2
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  have e1 : (s + 1 - 1) = s := by omega
  rw [e1]
  have e2 : (s + 1) * m = m * s + m := by ring
  rw [e2]
  omega

private theorem half_le_div_of_mul {p m : ℕ} (hp : 3 ≤ p) (hm : 1 ≤ m) :
    (m - 1) / 2 ≤ (p * m - 1) / (2 * (p - 1)) := by
  apply (Nat.le_div_iff_mul_le (by omega)).2
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e1 : (s + 1 - 1) = s := by omega
  have e2 : (n + 1 - 1) = n := by omega
  rw [e1, e2]
  have e3 : (s + 1) * (n + 1) - 1 = s * n + s + n := by
    have : (s + 1) * (n + 1) = s * n + s + n + 1 := by ring
    omega
  rw [e3]
  have h2 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
  have h3 : n / 2 * 2 * s ≤ n * s := Nat.mul_le_mul_right s h2
  nlinarith [h3]

theorem card_pGammaL2_lt_of_odd {p e : ℕ} (hp : 3 ≤ p) (he : 3 ≤ e) (heo : Odd e) :
    p ^ e * (p ^ (2 * e) - 1) * e < (p + 1) ^ ((p ^ e - 1) / (p - 1)) := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 3 := ⟨e - 3, by omega⟩
  have hpe : p ^ (f + 3) = p * p ^ (f + 2) := by ring
  have hm9 : 9 ≤ p ^ (f + 2) := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
      _ ≤ p ^ (f + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hN : p ^ (f + 2) ≤ (p ^ (f + 3) - 1) / (p - 1) := by
    rw [hpe]
    exact le_div_of_mul hp (by omega)
  calc p ^ (f + 3) * (p ^ (2 * (f + 3)) - 1) * (f + 3) ≤ (p ^ (f + 2)) ^ 5 := lhs_le_pow_five hp
    _ < 2 ^ (2 * p ^ (f + 2)) := pow_five_lt_two_pow_two_mul hm9
    _ = 4 ^ p ^ (f + 2) := by rw [pow_mul]; norm_num
    _ ≤ (p + 1) ^ p ^ (f + 2) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (p + 1) ^ ((p ^ (f + 3) - 1) / (p - 1)) := Nat.pow_le_pow_right (by omega) hN

theorem card_pGammaL2_lt_of_even {p e : ℕ} (hp : 3 ≤ p) (he : 4 ≤ e) :
    p ^ e * (p ^ (2 * e) - 1) * e < (p + 1) ^ ((p ^ e - 1) / (2 * (p - 1))) := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 3 := ⟨e - 3, by omega⟩
  have hpe : p ^ (f + 3) = p * p ^ (f + 2) := by ring
  have hm27 : 27 ≤ p ^ (f + 2) := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp 3
      _ ≤ p ^ (f + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hN : (p ^ (f + 2) - 1) / 2 ≤ (p ^ (f + 3) - 1) / (2 * (p - 1)) := by
    rw [hpe]
    exact half_le_div_of_mul hp (by omega)
  have hbig := five_lt_two_pow (j := p ^ (f + 2) - 2) (by omega)
  rw [show p ^ (f + 2) - 2 + 2 = p ^ (f + 2) by omega] at hbig
  calc p ^ (f + 3) * (p ^ (2 * (f + 3)) - 1) * (f + 3) ≤ (p ^ (f + 2)) ^ 5 := lhs_le_pow_five hp
    _ < 2 ^ (p ^ (f + 2) - 2) := hbig
    _ ≤ 2 ^ (2 * ((p ^ (f + 2) - 1) / 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 ^ ((p ^ (f + 2) - 1) / 2) := by rw [pow_mul]; norm_num
    _ ≤ (p + 1) ^ ((p ^ (f + 2) - 1) / 2) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (p + 1) ^ ((p ^ (f + 3) - 1) / (2 * (p - 1))) := Nat.pow_le_pow_right (by omega) hN

theorem succ_le_two_pow_orderOf {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    p + 1 ≤ 2 ^ orderOf (2 : ZMod p) := by
  have hp : p.Prime := Fact.out
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hpos : 0 < orderOf (2 : ZMod p) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one h2ne⟩
  have hpow : (2 : ZMod p) ^ orderOf (2 : ZMod p) = 1 := pow_orderOf_eq_one _
  have hdvd : p ∣ 2 ^ orderOf (2 : ZMod p) - 1 := by
    rw [← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow,
      Nat.cast_ofNat, hpow, Nat.cast_one, sub_self]
  have hgt : 1 < 2 ^ orderOf (2 : ZMod p) := Nat.one_lt_two_pow hpos.ne'
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

end
