module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.LocalAnalysis.GLTheoremA

theorem dvd_two_pow_sq_sub_of_rk2Ord_six {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : rk2Ord p n = 6) : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := by
  have h6 : rk2Ord p n ∣ 6 := by rw [h]
  have hdvd6 : p ∣ 2 ^ (n * 6) - 1 := (rk2Ord_dvd_iff (p := p) (n := n) 6).1 h6
  have hn3 : ¬ p ∣ 2 ^ (n * 3) - 1 := by
    intro h3
    have h36 : rk2Ord p n ∣ 3 := (rk2Ord_dvd_iff (p := p) (n := n) 3).2 h3
    rw [h] at h36
    exact absurd h36 (by norm_num)
  have hdvd3 : p ∣ 2 ^ (n * 3) + 1 := by
    have hfac : 2 ^ (n * 6) - 1 = (2 ^ (n * 3) - 1) * (2 ^ (n * 3) + 1) := by
      have h2 : 2 ^ (n * 6) = (2 ^ (n * 3)) ^ 2 := by
        rw [show n * 6 = (n * 3) * 2 by ring, pow_mul]
      have hsq := Nat.sq_sub_sq (2 ^ (n * 3)) 1
      rw [one_pow] at hsq
      rw [h2, hsq, mul_comm]
    rcases hp.dvd_mul.1 (hfac ▸ hdvd6) with h' | h'
    · exact absurd h' hn3
    · exact h'
  have hnot2 : ¬ p ∣ 2 ^ n + 1 := by
    intro h2
    have h2' : rk2Ord p n = 2 := (rk2Ord_eq_two_iff hp hp2).2 h2
    omega
  have hfac2 : 2 ^ (n * 3) + 1 = (2 ^ n + 1) * ((2 ^ n) ^ 2 - 2 ^ n + 1) := by
    set q := 2 ^ n with hq
    have hq1 : 1 ≤ q := Nat.one_le_two_pow
    have hq2 : q ≤ q ^ 2 := by nlinarith
    have hq3 : 2 ^ (n * 3) = q ^ 3 := by
      rw [hq, show n * 3 = n * 3 by rfl, pow_mul]
    rw [hq3]
    zify [hq1, hq2]
    ring
  rcases hp.dvd_mul.1 (hfac2 ▸ hdvd3) with h' | h'
  · exact absurd h' hnot2
  · exact h'

theorem seven_le_of_rk2Ord_six {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : rk2Ord p n = 6) : 7 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := by
      have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rwa [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  have hpow : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  have hdvd : orderOf ((2 : ZMod p) ^ n) ∣ p - 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [← pow_mul, mul_comm n (p - 1), pow_mul, hpow, one_pow]
  have h6 : orderOf ((2 : ZMod p) ^ n) = 6 := h
  rw [h6] at hdvd
  have hp2' : 2 ≤ p := hp.two_le
  omega

theorem two_lt_two_pow_of_rk2Ord_six {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : rk2Ord p n = 6) : 2 < 2 ^ n := by
  have hdvd := dvd_two_pow_sq_sub_of_rk2Ord_six hp hp2 h
  have hp7 := seven_le_of_rk2Ord_six hp hp2 h
  by_contra hle
  push Not at hle
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hq : 2 ^ n = 1 ∨ 2 ^ n = 2 := by omega
  rcases hq with h1 | h2
  · rw [h1] at hdvd
    norm_num at hdvd
    omega
  · rw [h2] at hdvd
    have h3 : p ∣ 3 := by simpa using hdvd
    have := Nat.le_of_dvd (by norm_num) h3
    omega

end CFSG.LocalAnalysis.GLTheoremA.Y10F
