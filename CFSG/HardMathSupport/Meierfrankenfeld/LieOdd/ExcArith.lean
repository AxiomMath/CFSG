module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Arith
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem pow_nine_le_two_pow {x : ℕ} (hx : 81 ≤ x) : 2048 * x ^ 9 ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 81 * (n + 1) ≤ 82 * n := by omega
    have h2 : 81 ^ 9 * (n + 1) ^ 9 ≤ 82 ^ 9 * n ^ 9 := by
      have := Nat.pow_le_pow_left h1 9
      rw [mul_pow, mul_pow] at this
      exact this
    have h82 : 82 ^ 9 ≤ 2 * 81 ^ 9 := by norm_num
    have h3 : 81 ^ 9 * (n + 1) ^ 9 ≤ 81 ^ 9 * (2 * n ^ 9) := by
      calc 81 ^ 9 * (n + 1) ^ 9 ≤ 82 ^ 9 * n ^ 9 := h2
        _ ≤ 2 * 81 ^ 9 * n ^ 9 := Nat.mul_le_mul_right _ h82
        _ = 81 ^ 9 * (2 * n ^ 9) := by ring
    have h4 : (n + 1) ^ 9 ≤ 2 * n ^ 9 :=
      Nat.le_of_mul_le_mul_left h3 (by positivity)
    calc 2048 * (n + 1) ^ 9 ≤ 2048 * (2 * n ^ 9) := Nat.mul_le_mul_left _ h4
      _ = 2 * (2048 * n ^ 9) := by ring
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (n + 1) := by ring

theorem two_pow_bound_exc {k : ℕ} (hk : 4 ≤ k) :
    ∀ q : ℕ, 3 ≤ q → 2048 * q ^ (2 * k ^ 2 + 1) ≤ 2 ^ (q ^ k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro q hq
    have hx : 81 ≤ q ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have h1 : q ^ (2 * 4 ^ 2 + 1) ≤ (q ^ 4) ^ 9 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by norm_num)
    calc 2048 * q ^ (2 * 4 ^ 2 + 1) ≤ 2048 * (q ^ 4) ^ 9 := Nat.mul_le_mul_left _ h1
      _ ≤ 2 ^ (q ^ 4) := pow_nine_le_two_pow hx
  | succ k hk ih =>
    intro q hq
    have hx : 81 ≤ q ^ k := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        _ ≤ q ^ k := Nat.pow_le_pow_left hq k
    have h3a : q ^ (4 * k + 2) ≤ (q ^ k) ^ 9 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have h3b : (q ^ k) ^ 9 ≤ 2 ^ (q ^ k) := by
      have := pow_nine_le_two_pow hx
      linarith [Nat.zero_le ((q ^ k) ^ 9)]
    have h3 : q ^ (4 * k + 2) ≤ 2 ^ (q ^ k) := le_trans h3a h3b
    calc 2048 * q ^ (2 * (k + 1) ^ 2 + 1)
        = (2048 * q ^ (2 * k ^ 2 + 1)) * q ^ (4 * k + 2) := by
          rw [show 2 * (k + 1) ^ 2 + 1 = (2 * k ^ 2 + 1) + (4 * k + 2) by ring, pow_add]
          ring
      _ ≤ 2 ^ (q ^ k) * 2 ^ (q ^ k) := Nat.mul_le_mul (ih q hq) h3
      _ = 2 ^ (q ^ k + q ^ k) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (q ^ (k + 1)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [pow_succ]
          nlinarith [Nat.zero_le (q ^ k)]

theorem two_le_orderOf_two_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    2 ≤ orderOf (2 : ZMod p) := by
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  by_contra hlt
  have h1 : orderOf (2 : ZMod p) ≤ 1 := by omega
  have h2 : 2 ^ orderOf (2 : ZMod p) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : p + 1 ≤ 2 ^ orderOf (2 : ZMod p) := succ_le_two_pow_orderOf hp2
  norm_num at h2
  omega

theorem card_aut_exc_lt {p e k D : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (hk : 4 ≤ k)
    (hD : D ≤ 2 * k ^ 2) :
    1024 * e * (p ^ e) ^ D <
      2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) / 2 * (p ^ e) ^ k / (p - 1))) := by
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  obtain ⟨m, hm⟩ := hpp.odd_of_ne_two hp2
  have hm0 : 0 < m := by omega
  have hpm : p - 1 = m * 2 := by omega
  have hpq : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  have hqe : e < p ^ e := Nat.lt_pow_self (by omega)
  have hq3 : 3 ≤ p ^ e := le_trans hp3 hpq
  have hN : (p ^ e) ^ k / 2 ≤ (p ^ e - 1) / 2 * (p ^ e) ^ k / (p - 1) := by
    have hq1 : m ≤ (p ^ e - 1) / 2 := by omega
    have hA : m * (p ^ e) ^ k ≤ (p ^ e - 1) / 2 * (p ^ e) ^ k :=
      Nat.mul_le_mul_right _ hq1
    rw [hpm]
    calc (p ^ e) ^ k / 2 = m * (p ^ e) ^ k / (m * 2) :=
          (Nat.mul_div_mul_left _ _ hm0).symm
      _ ≤ (p ^ e - 1) / 2 * (p ^ e) ^ k / (m * 2) := Nat.div_le_div_right hA
  have hord2 := two_le_orderOf_two_zmod (p := p) hp2
  have hX := two_pow_bound_exc hk (p ^ e) hq3
  have hqD : 0 < (p ^ e) ^ D := by positivity
  have hDq : (p ^ e) ^ D ≤ (p ^ e) ^ (2 * k ^ 2 + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hlt1 : e * (p ^ e) ^ D < p ^ e * (p ^ e) ^ D := by
    nlinarith [hqe, hqD]
  have hlt2 : p ^ e * (p ^ e) ^ D ≤ (p ^ e) ^ (2 * k ^ 2 + 1) := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have key : 2 * (1024 * e * (p ^ e) ^ D) < 2 ^ ((p ^ e) ^ k) := by
    have h1 : 2 * (1024 * e * (p ^ e) ^ D) = 2048 * (e * (p ^ e) ^ D) := by ring
    have h2 : 2048 * (e * (p ^ e) ^ D) < 2048 * (p ^ e) ^ (2 * k ^ 2 + 1) := by
      have := lt_of_lt_of_le hlt1 hlt2
      omega
    rw [h1]
    omega
  have hON : 2 * ((p ^ e - 1) / 2 * (p ^ e) ^ k / (p - 1)) ≤
      orderOf (2 : ZMod p) * ((p ^ e - 1) / 2 * (p ^ e) ^ k / (p - 1)) :=
    Nat.mul_le_mul_right _ hord2
  have hexp : (p ^ e) ^ k ≤ 1 + orderOf (2 : ZMod p) * ((p ^ e - 1) / 2 * (p ^ e) ^ k / (p - 1)) := by
    generalize (p ^ e - 1) / 2 * (p ^ e) ^ k / (p - 1) = N at hN hON ⊢
    generalize orderOf (2 : ZMod p) * N = Y at hON ⊢
    generalize (p ^ e) ^ k = x at hN hON ⊢
    omega
  have hpow : 2 ^ ((p ^ e) ^ k) ≤ 2 ^ (1 + orderOf (2 : ZMod p) *
      ((p ^ e - 1) / 2 * (p ^ e) ^ k / (p - 1))) := Nat.pow_le_pow_right (by norm_num) hexp
  rw [pow_add, pow_one] at hpow
  linarith

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

end
