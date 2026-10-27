module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Arith

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem tri_aux (m : ℕ) : (m + 7) * (m + 6) / 2 + 5 ≤ 3 ^ (m + 3) := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    have hev : 2 * ((k + 7) * (k + 6) / 2) = (k + 7) * (k + 6) := by
      apply Nat.two_mul_div_two_of_even
      rw [mul_comm]
      exact Nat.even_mul_succ_self (k + 6)
    have hP : k + 1 ≤ (k + 7) * (k + 6) := by nlinarith
    have e2 : (k + 1 + 7) * (k + 1 + 6) = (k + 7) * (k + 6) + 2 * (k + 7) := by ring
    have e3 : 3 ^ (k + 1 + 3) = 3 * 3 ^ (k + 3) := by ring
    rw [e2, e3]
    generalize (k + 7) * (k + 6) = P at hev hP ih ⊢
    generalize 3 ^ (k + 3) = X at ih ⊢
    omega

theorem tri_add_five_le_three_pow {n : ℕ} (hn : 7 ≤ n) :
    n * (n - 1) / 2 + 5 ≤ 3 ^ (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h1 : m + 7 - 1 = m + 6 := by omega
  have h2 : m + 7 - 4 = m + 3 := by omega
  rw [h1, h2]
  exact tri_aux m

theorem ninety_six_mul_le_three_pow_add_four {e : ℕ} (he : 1 ≤ e) :
    96 * e ≤ 3 ^ (e + 4) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ]
    omega

theorem lin_le_pow_of_le {K T : ℕ} (hK : T + 5 ≤ K) {e : ℕ} (he : 1 ≤ e) :
    e * (T + 4) + 1 ≤ K ^ e := by
  induction e, he using Nat.le_induction with
  | base =>
    rw [pow_one]
    omega
  | succ k hk ih =>
    rw [pow_succ]
    have h1 : (k * (T + 4) + 1) * (T + 4 + 1) ≤ K ^ k * K :=
      Nat.mul_le_mul ih (by omega)
    nlinarith [Nat.zero_le (k * (T + 4) * (T + 4))]

theorem card_aut_pomega_lt {p e n : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hn : 7 ≤ n) :
    96 * p ^ (e * (n * (n - 1) / 2)) * e <
      2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) * p ^ (e * (n - 4)) / (p - 1))) := by
  have hp : p.Prime := hpf.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hd := succ_le_two_pow_orderOf (p := p) hp2
  have hT := tri_add_five_le_three_pow hn
  have hN : p ^ (e * (n - 4)) ≤ (p ^ e - 1) * p ^ (e * (n - 4)) / (p - 1) := by
    have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact Nat.mul_le_mul (by omega) le_rfl
  have hK' : (3 ^ (n - 4)) ^ e ≤ p ^ (e * (n - 4)) := by
    rw [← pow_mul, mul_comm (n - 4) e]
    exact Nat.pow_le_pow_left hp3 _
  have hlin := lin_le_pow_of_le hT he
  have hNbig : e * (n * (n - 1) / 2 + 4) + 1 ≤
      (p ^ e - 1) * p ^ (e * (n - 4)) / (p - 1) :=
    le_trans hlin (le_trans hK' hN)
  set T := n * (n - 1) / 2 with hTdef
  set N := (p ^ e - 1) * p ^ (e * (n - 4)) / (p - 1) with hNdef
  have hexp : e * (T + 4) = e * T + 4 * e := by ring
  have hMN : e * T + (e + 4) ≤ N := by linarith
  have h96 : 96 * e ≤ p ^ (e + 4) :=
    le_trans (ninety_six_mul_le_three_pow_add_four he) (Nat.pow_le_pow_left hp3 _)
  have hchain : 96 * p ^ (e * T) * e ≤ p ^ (e * T) * p ^ (e + 4) := by
    calc 96 * p ^ (e * T) * e = p ^ (e * T) * (96 * e) := by ring
      _ ≤ p ^ (e * T) * p ^ (e + 4) := Nat.mul_le_mul_left _ h96
  have hpN : p ^ (e * T + (e + 4)) ≤ p ^ N := Nat.pow_le_pow_right (by omega) hMN
  have hNpos : N ≠ 0 := by omega
  have hpN' : p ^ N < (p + 1) ^ N := Nat.pow_lt_pow_left (by omega) hNpos
  have hfin : (p + 1) ^ N ≤ 2 ^ (orderOf (2 : ZMod p) * N) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hd N
  calc 96 * p ^ (e * T) * e ≤ p ^ (e * T) * p ^ (e + 4) := hchain
    _ = p ^ (e * T + (e + 4)) := (pow_add _ _ _).symm
    _ ≤ p ^ N := hpN
    _ < (p + 1) ^ N := hpN'
    _ ≤ 2 ^ (orderOf (2 : ZMod p) * N) := hfin

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

end
