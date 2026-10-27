module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Arith
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem card_aut_pspn_lt_of_le {p e r d N : ℕ} (hp : 3 ≤ p) (he : 1 ≤ e)
    (hN : e * (2 * r ^ 2 + r + 1) ≤ N) (hd : p + 1 ≤ 2 ^ d) :
    p ^ (e * (2 * r ^ 2 + r)) * e < 2 ^ (d * N) := by
  have h1 : e < p ^ e := Nat.lt_pow_self (by omega)
  have hN1 : 1 ≤ N :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) hN
  calc p ^ (e * (2 * r ^ 2 + r)) * e < p ^ (e * (2 * r ^ 2 + r)) * p ^ e :=
        Nat.mul_lt_mul_of_pos_left h1 (pow_pos (by omega) _)
    _ = p ^ (e * (2 * r ^ 2 + r + 1)) := by
        rw [← pow_add]
        ring_nf
    _ ≤ p ^ N := Nat.pow_le_pow_right (by omega) hN
    _ < (p + 1) ^ N := Nat.pow_lt_pow_left (by omega) (by omega)
    _ ≤ (2 ^ d) ^ N := Nat.pow_le_pow_left hd N
    _ = 2 ^ (d * N) := by rw [← pow_mul]

theorem spN_eq {p k : ℕ} (hp : 2 ≤ p) :
    (p ^ k - 1) / (2 * (p - 1)) = (∑ i ∈ Finset.range k, p ^ i) / 2 := by
  rw [Nat.geomSum_eq hp, Nat.div_div_eq_div_mul, mul_comm]

theorem geomSum_le_geomSum {a b : ℕ} (hab : a ≤ b) (k : ℕ) :
    ∑ i ∈ Finset.range k, a ^ i ≤ ∑ i ∈ Finset.range k, b ^ i :=
  Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left hab i

theorem two_mul_geomSum_three (k : ℕ) : 2 * ∑ i ∈ Finset.range k, 3 ^ i = 3 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    omega

theorem three_pow_le_four_mul_spN {p k : ℕ} (hp : 3 ≤ p) :
    3 ^ k ≤ 4 * ((p ^ k - 1) / (2 * (p - 1))) + 3 := by
  rw [spN_eq (by omega)]
  have h1 := geomSum_le_geomSum hp k
  have h2 := two_mul_geomSum_three k
  have h3 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem geomSum_le_two_mul_spN {b p k : ℕ} (hb : b ≤ p) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range k, b ^ i ≤ 2 * ((p ^ k - 1) / (2 * (p - 1))) + 1 := by
  rw [spN_eq hp]
  have h1 := geomSum_le_geomSum hb k
  omega

theorem sp_poly_le_three_pow {r : ℕ} (hr : 5 ≤ r) : 4 * (2 * r ^ 2 + r + 1) + 4 ≤ 3 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [pow_succ 3 r]
    nlinarith

theorem le_three_pow_pred (e : ℕ) : e ≤ 3 ^ (e - 1) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact Nat.zero_le _
  · have := Nat.lt_pow_self (show 1 < 3 by norm_num) (n := e - 1)
    omega

theorem lin_le_three_pow {c k e₀ e : ℕ} (hk : 1 ≤ k) (he₀ : 1 ≤ e₀) (he : e₀ ≤ e)
    (h0 : c * e₀ + 7 ≤ 3 ^ (k * e₀)) : c * e + 7 ≤ 3 ^ (k * e) := by
  induction e, he using Nat.le_induction with
  | base => exact h0
  | succ e he ih =>
    rw [show k * (e + 1) = k * e + k by ring, pow_add]
    have h3 : 3 ≤ 3 ^ k := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have he1 : 1 ≤ e := le_trans he₀ he
    have hmul : (c * e + 7) * 3 ≤ 3 ^ (k * e) * 3 ^ k :=
      Nat.mul_le_mul ih h3
    have hce : c ≤ c * e := Nat.le_mul_of_pos_right c he1
    nlinarith

theorem orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_thirteen : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_seventeen : orderOf (2 : ZMod 17) = 8 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_nineteen : orderOf (2 : ZMod 19) = 18 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m
  decide

theorem card_aut_pspn_lt {p e r : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (he : 1 ≤ e) (h2 : ¬ (r = 2 ∧ p ^ e ≤ 7)) (h3 : ¬ (r = 3 ∧ p ^ e = 3))
    (h4 : ¬ (r = 4 ∧ p ^ e = 3)) :
    p ^ (e * (2 * r ^ 2 + r)) * e <
      2 ^ (orderOf (2 : ZMod p) * ((p ^ (e * r) - 1) / (2 * (p - 1)))) := by
  have hp : p.Prime := hpf.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hd := succ_le_two_pow_orderOf (p := p) hp2
  have hN3 := three_pow_le_four_mul_spN (k := e * r) hp3
  suffices hcrude : e * (2 * r ^ 2 + r + 1) ≤ (p ^ (e * r) - 1) / (2 * (p - 1)) ∨
      p ^ (e * (2 * r ^ 2 + r)) * e <
        2 ^ (orderOf (2 : ZMod p) * ((p ^ (e * r) - 1) / (2 * (p - 1)))) by
    rcases hcrude with h | h
    · exact card_aut_pspn_lt_of_le hp3 he h hd
    · exact h
  rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with rfl | rfl | rfl | hr5
  ·
    rcases (show e = 1 ∨ e = 2 ∨ 3 ≤ e by omega) with rfl | rfl | he3
    ·
      have hp7 : 7 < p := by
        by_contra h
        exact h2 ⟨rfl, by simpa using (not_lt.mp h)⟩
      have hS : ∑ i ∈ Finset.range 2, p ^ i = 1 + p := by simp [Finset.sum_range_succ]
      have hN : (p ^ (1 * 2) - 1) / (2 * (p - 1)) = (1 + p) / 2 := by
        rw [spN_eq (by omega), hS]
      rw [hN]
      by_cases h23 : 23 ≤ p
      · left
        omega
      · right
        have hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 := by
          interval_cases p <;> first | omega | (exfalso; norm_num at hp)
        rcases hcases with rfl | rfl | rfl | rfl
        · rw [orderOf_two_zmod_eleven]; norm_num
        · rw [orderOf_two_zmod_thirteen]; norm_num
        · rw [orderOf_two_zmod_seventeen]; norm_num
        · rw [orderOf_two_zmod_nineteen]; norm_num
    ·
      by_cases hp5 : 5 ≤ p
      · left
        have hg := geomSum_le_two_mul_spN (k := 2 * 2) hp5 (by omega)
        have h156 : ∑ i ∈ Finset.range (2 * 2), 5 ^ i = 156 := by
          simp [Finset.sum_range_succ]
        rw [h156] at hg
        omega
      · right
        have : p = 3 := by
          rcases (show p = 3 ∨ p = 4 by omega) with h | h
          · exact h
          · rw [h] at hp; norm_num at hp
        subst this
        rw [orderOf_two_zmod_three]
        norm_num
    ·
      left
      have h1 : 3 ^ (e * 2) ≤ 4 * ((p ^ (e * 2) - 1) / (2 * (p - 1))) + 3 := hN3
      have h2' : 44 * e + 7 ≤ 3 ^ (2 * e) :=
        lin_le_three_pow (k := 2) (e₀ := 3) (by norm_num) (by norm_num) he3 (by norm_num)
      rw [mul_comm 2 e] at h2'
      omega
  ·
    rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | he2
    · by_cases hp7 : 7 ≤ p
      · left
        have hg := geomSum_le_two_mul_spN (k := 1 * 3) hp7 (by omega)
        have h57 : ∑ i ∈ Finset.range (1 * 3), 7 ^ i = 57 := by
          simp [Finset.sum_range_succ]
        rw [h57] at hg
        omega
      · right
        have hp5 : p = 5 := by
          rcases (show p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 by omega) with h | h | h | h
          · exact absurd ⟨rfl, by rw [h]; norm_num⟩ h3
          · rw [h] at hp; norm_num at hp
          · exact h
          · rw [h] at hp; norm_num at hp
        subst hp5
        rw [orderOf_two_zmod_five]
        norm_num
    · left
      have h1 : 3 ^ (e * 3) ≤ 4 * ((p ^ (e * 3) - 1) / (2 * (p - 1))) + 3 := hN3
      have h2' : 88 * e + 7 ≤ 3 ^ (3 * e) :=
        lin_le_three_pow (k := 3) (e₀ := 2) (by norm_num) (by norm_num) he2 (by norm_num)
      rw [mul_comm 3 e] at h2'
      omega
  ·
    left
    rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | he2
    · have hp5 : 5 ≤ p := by
        by_contra h
        have : p = 3 ∨ p = 4 := by omega
        rcases this with h' | h'
        · exact h4 ⟨rfl, by rw [h']; norm_num⟩
        · rw [h'] at hp; norm_num at hp
      have hg := geomSum_le_two_mul_spN (k := 1 * 4) hp5 (by omega)
      have h156 : ∑ i ∈ Finset.range (1 * 4), 5 ^ i = 156 := by
        simp [Finset.sum_range_succ]
      rw [h156] at hg
      omega
    · have h1 : 3 ^ (e * 4) ≤ 4 * ((p ^ (e * 4) - 1) / (2 * (p - 1))) + 3 := hN3
      have h2' : 148 * e + 7 ≤ 3 ^ (4 * e) :=
        lin_le_three_pow (k := 4) (e₀ := 2) (by norm_num) (by norm_num) he2 (by norm_num)
      rw [mul_comm 4 e] at h2'
      omega
  ·
    left
    have hpoly := sp_poly_le_three_pow hr5
    have he' : e ≤ 3 ^ (e - 1) := le_three_pow_pred e
    have hsplit : 3 ^ (e * r) = 3 ^ r * 3 ^ (r * (e - 1)) := by
      rw [← pow_add]
      congr 1
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    have he'' : 3 ^ (e - 1) ≤ 3 ^ (r * (e - 1)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
    have hmain : (4 * (2 * r ^ 2 + r + 1) + 4) * e ≤ 3 ^ (e * r) := by
      rw [hsplit]
      exact Nat.mul_le_mul hpoly (he'.trans he'')
    have key : 4 * (e * (2 * r ^ 2 + r + 1)) + 4 ≤ 4 * ((p ^ (e * r) - 1) / (2 * (p - 1))) + 3 + 1 := by
      have : 4 * (e * (2 * r ^ 2 + r + 1)) + 4 ≤ (4 * (2 * r ^ 2 + r + 1) + 4) * e := by
        nlinarith
      omega
    omega

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
