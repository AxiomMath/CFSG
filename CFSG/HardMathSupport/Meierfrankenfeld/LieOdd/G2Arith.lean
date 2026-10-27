module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitArith

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem card_aut_g2_lt {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (h3 : p ^ e ≠ 3) :
    24 * e * (p ^ e) ^ 14 <
      2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) / 2 * (p ^ e) ^ 2 / (p - 1))) := by
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  by_cases hexc : p = 5 ∧ e = 1
  · obtain ⟨rfl, rfl⟩ := hexc
    rw [orderOf_two_zmod_five]
    norm_num
  · have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    have hq5 : p ^ e ≠ 5 := by
      intro h5
      rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | he2
      · rw [pow_one] at h5
        exact hexc ⟨h5, rfl⟩
      · have h9 : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right (by omega) he2
        have : 9 ≤ p ^ 2 := by nlinarith
        omega
    have hodd : Odd (p ^ e) := (hpp.odd_of_ne_two hp2).pow
    obtain ⟨h, hh⟩ := hodd
    obtain ⟨q, hq⟩ : ∃ q, q = p ^ e := ⟨_, rfl⟩
    rw [← hq] at hh hpe h3 hq5 ⊢
    have hdiv : (q - 1) / 2 = h := by omega
    rw [hdiv]
    have hq7 : 7 ≤ q := by omega
    have hp1 : p - 1 ≤ 2 * h := by omega
    have hpos : 0 < p - 1 := by omega
    have hM2 : 2 * h * (h + 1) ≤ h * q ^ 2 / (p - 1) := by
      rw [Nat.le_div_iff_mul_le hpos]
      have h1 : 2 * h * (h + 1) * (p - 1) ≤ 2 * h * (h + 1) * (2 * h) :=
        Nat.mul_le_mul_left _ hp1
      have h2 : q ^ 2 = (2 * h + 1) ^ 2 := by rw [hh]
      rw [h2]
      nlinarith
    set M := h * q ^ 2 / (p - 1) with hMdef
    have hqsq : q ^ 2 ≤ 2 * M + 1 := by
      have : q ^ 2 = 4 * h ^ 2 + 4 * h + 1 := by rw [hh]; ring
      nlinarith
    have hqe : 28 * e + 5 ≤ q ^ 2 := by
      rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | he2
      · rw [pow_one] at hq
        subst hq
        nlinarith
      · have hsq : q ^ 2 = (p ^ 2) ^ e := by rw [hq, ← pow_mul, ← pow_mul, mul_comm]
        have h9 : 9 ^ e ≤ (p ^ 2) ^ e := Nat.pow_le_pow_left (by nlinarith) e
        have hnine : ∀ n, 2 ≤ n → 28 * n + 5 ≤ 9 ^ n := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => norm_num
          | succ k hk ih => rw [pow_succ]; omega
        have := hnine e he2
        omega
    have hMe : e * 14 + 2 ≤ M := by omega
    have hord : p + 1 ≤ 2 ^ orderOf (2 : ZMod p) := succ_le_two_pow_orderOf hp2
    have hpow : (p + 1) ^ M ≤ 2 ^ (orderOf (2 : ZMod p) * M) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left hord M
    have hc : 24 * e < (M - e * 14) * (p + M) := by
      have ht : 2 ≤ M - e * 14 := by omega
      have : 2 * (p + M) ≤ (M - e * 14) * (p + M) := Nat.mul_le_mul_right _ ht
      omega
    have key : 24 * e * p ^ (e * 14) < (p + 1) ^ M :=
      mul_pow_lt_succ_pow_of_gap (by omega) (by omega) hc
    calc 24 * e * (q) ^ 14 = 24 * e * p ^ (e * 14) := by rw [hq, ← pow_mul]
      _ < (p + 1) ^ M := key
      _ ≤ 2 ^ (orderOf (2 : ZMod p) * M) := hpow

theorem succ_pow_fifteen_lt_eight_mul {n : ℕ} (hn : 9 ≤ n) : (n + 1) ^ 15 < 8 * n ^ 15 := by
  have hA : 9 * (n + 1) ≤ 10 * n := by omega
  have hB : (9 * (n + 1)) ^ 15 ≤ (10 * n) ^ 15 := Nat.pow_le_pow_left hA 15
  rw [mul_pow, mul_pow] at hB
  have hc : (10 : ℕ) ^ 15 < 8 * 9 ^ 15 := by norm_num
  have hpos : 0 < n ^ 15 := pow_pos (by omega) 15
  have h2 : 9 ^ 15 * (n + 1) ^ 15 < 9 ^ 15 * (8 * n ^ 15) := by
    have h3 : 10 ^ 15 * n ^ 15 < 8 * 9 ^ 15 * n ^ 15 := by
      nlinarith
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left h2

theorem twentyfour_pow_fifteen_lt_two_pow_sq {n : ℕ} (hn : 9 ≤ n) :
    24 * n ^ 15 < 2 ^ (n ^ 2 - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1) ^ 15 < 8 * k ^ 15 := succ_pow_fifteen_lt_eight_mul hk
    have h2 : 24 * (k + 1) ^ 15 < 2 ^ (k ^ 2 - 1) * 2 ^ 3 := by
      calc 24 * (k + 1) ^ 15 < 24 * (8 * k ^ 15) :=
            Nat.mul_lt_mul_of_pos_left h1 (by norm_num)
        _ = 8 * (24 * k ^ 15) := by ring
        _ < 8 * 2 ^ (k ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 2 ^ (k ^ 2 - 1) * 2 ^ 3 := by ring
    have hexp : (k + 1) ^ 2 - 1 = (k ^ 2 - 1) + (2 * k + 1) := by
      have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
      have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      omega
    have h8 : 2 ^ 3 ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2' : 24 * (k + 1) ^ 15 < 2 ^ (k ^ 2 - 1) * 2 ^ (2 * k + 1) :=
      lt_of_lt_of_le h2 (Nat.mul_le_mul_left _ h8)
    rw [hexp, pow_add]
    exact h2'

theorem card_aut_g2_three_lt {e : ℕ} (he : 2 ≤ e) :
    24 * e * (3 ^ e) ^ 14 < 2 ^ ((((3 ^ e) ^ 2 - 1) / (3 - 1)) * orderOf (2 : ZMod 3)) := by
  rw [orderOf_two_zmod_three]
  have hq9 : 9 ≤ 3 ^ e := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hee : e < 3 ^ e := Nat.lt_pow_self (by norm_num)
  have hdiv : (((3 ^ e) ^ 2 - 1) / (3 - 1)) * 2 = (3 ^ e) ^ 2 - 1 := by
    obtain ⟨k, hk⟩ : Odd (3 ^ e) := Odd.pow (by decide)
    have hsq : (3 ^ e) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by
      rw [hk]; ring
    rw [hsq, Nat.add_sub_cancel, show (3 : ℕ) - 1 = 2 from rfl,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_comm]
  rw [hdiv]
  have hlhs : 24 * e * (3 ^ e) ^ 14 ≤ 24 * (3 ^ e) ^ 15 := by
    have : e * (3 ^ e) ^ 14 ≤ (3 ^ e) ^ 15 := by
      calc e * (3 ^ e) ^ 14 ≤ (3 ^ e) * (3 ^ e) ^ 14 := Nat.mul_le_mul_right _ hee.le
        _ = (3 ^ e) ^ 15 := by ring
    calc 24 * e * (3 ^ e) ^ 14 = 24 * (e * (3 ^ e) ^ 14) := by ring
      _ ≤ 24 * (3 ^ e) ^ 15 := Nat.mul_le_mul_left _ this
  exact lt_of_le_of_lt hlhs (twentyfour_pow_fifteen_lt_two_pow_sq hq9)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
