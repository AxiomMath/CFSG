module

public import CFSG.FeitThompson.OddOrder.GeometricSumCongruences

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

theorem two_le_of_not_dvd_sub_one {p q : ℕ} (hpq : ¬ q ∣ (p - 1)) : 2 ≤ p := by
  by_contra h
  simp [show p - 1 = 0 by omega] at hpq

theorem coprime_sum_range_pow_sub_one {p q : ℕ} (hq : q.Prime) (hpq : ¬ q ∣ (p - 1)) :
    Nat.Coprime (∑ i ∈ range q, p ^ i) (p - 1) := by
  have hp := two_le_of_not_dvd_sub_one hpq
  unfold Nat.Coprime
  rw [gcd_sum_range_pow_sub_one (by omega) q]
  exact hq.coprime_iff_not_dvd.2 hpq

theorem prime_modEq_one_of_dvd_sum_range_pow {p q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hpq : ¬ q ∣ (p - 1)) (hrN : r ∣ ∑ i ∈ range q, p ^ i) : r ≡ 1 [MOD q] := by
  have hp : 2 ≤ p := two_le_of_not_dvd_sub_one hpq
  have := Fact.mk hr
  have := Fact.mk hq
  have hrp1 : ¬ r ∣ (p - 1) := by
    intro h
    have hd := Nat.dvd_gcd hrN h
    rw [coprime_sum_range_pow_sub_one hq hpq] at hd
    exact hr.one_lt.ne' (Nat.dvd_one.1 hd)
  set x : ZMod r := (p : ZMod r) with hxdef
  have hx1 : x - 1 ≠ 0 := by
    have hcast : x - 1 = ((p - 1 : ℕ) : ZMod r) := by
      rw [Nat.cast_sub (by omega)]; simp [hxdef]
    rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
    exact hrp1
  have hxq : x ^ q = 1 := by
    have hgs := geom_sum_mul (x := x) q
    have hzero : (∑ i ∈ range q, x ^ i) = 0 := by
      have hc : (∑ i ∈ range q, x ^ i) = ((∑ i ∈ range q, p ^ i : ℕ) : ZMod r) := by
        push_cast; ring
      rw [hc, ZMod.natCast_eq_zero_iff]
      exact hrN
    rw [hzero, zero_mul] at hgs
    linear_combination -hgs
  have hxne1 : x ≠ 1 := fun h => hx1 (by rw [h]; ring)
  have hxne0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow hq.pos.ne'] at hxq
    exact zero_ne_one hxq
  have hdvd : q ∣ r - 1 := orderOf_eq_prime hxq hxne1 ▸ ZMod.orderOf_dvd_card_sub_one hxne0
  exact ((Nat.modEq_iff_dvd' hr.one_lt.le).2 hdvd).symm

theorem modEq_one_of_dvd_sum_range_pow {p q : ℕ} (hq : q.Prime) (hpq : ¬ q ∣ (p - 1)) :
    ∀ b, 0 < b → b ∣ (∑ i ∈ range q, p ^ i) → b ≡ 1 [MOD q] := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb0 hbN
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hb0.ne') with h1 | h1
    · rw [← h1]
    ·
      set r := b.minFac with hrdef
      have hr : r.Prime := Nat.minFac_prime h1.ne'
      have hrb : r ∣ b := Nat.minFac_dvd b
      have hlt : b / r < b := Nat.div_lt_self hb0 hr.one_lt
      have hb0' : 0 < b / r := Nat.div_pos (Nat.minFac_le hb0) hr.pos
      have hrec := ih (b / r) hlt hb0' ((Nat.div_dvd_of_dvd hrb).trans hbN)
      have hprime := prime_modEq_one_of_dvd_sum_range_pow hq hr hpq (hrb.trans hbN)
      rw [show b = r * (b / r) from (Nat.mul_div_cancel' hrb).symm]
      simpa using hprime.mul hrec

theorem modEq_one_of_dvd_sum_range_pow_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (_hpq : p ≠ q) (hmod : ¬ p ≡ 1 [MOD q]) {b : ℕ} (hb : 0 < b)
    (hbN : b ∣ ∑ i ∈ range q, p ^ i) : b ≡ 1 [MOD q] :=
  modEq_one_of_dvd_sum_range_pow hq
    (fun h => hmod ((Nat.modEq_iff_dvd' hp.one_lt.le).2 h).symm) b hb hbN

theorem modEq_one_of_dvd_pow_sub_one_div_sub_one {p q : ℕ} (hq : q.Prime)
    (hpq : ¬ q ∣ (p - 1)) {b : ℕ} (hb : 0 < b) (hbN : b ∣ (p ^ q - 1) / (p - 1)) :
    b ≡ 1 [MOD q] :=
  modEq_one_of_dvd_sum_range_pow hq hpq b hb
    (by rwa [sum_range_pow_eq_div (two_le_of_not_dvd_sub_one hpq) q])

theorem dvd_sub_one_of_dvd_sum_range_pow {p q : ℕ} (hq : q.Prime) (hpq : ¬ q ∣ (p - 1)) {b : ℕ}
    (hb : 0 < b) (hbN : b ∣ ∑ i ∈ range q, p ^ i) : q ∣ b - 1 :=
  (Nat.modEq_iff_dvd' hb).1 (modEq_one_of_dvd_sum_range_pow hq hpq b hb hbN).symm

end CFSG.FeitThompson
