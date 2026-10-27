module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

private theorem forty_mul_pow_eight_lt_four_pow {y : ℕ} (hy : 27 ≤ y) :
    40 * y ^ 8 < 4 ^ y := by
  induction y, hy using Nat.le_induction with
  | base => norm_num
  | succ y hy ih =>
    have hstep : 27 * (y + 1) ≤ 28 * y := by omega
    have hpow : 27 ^ 8 * (y + 1) ^ 8 ≤ 28 ^ 8 * y ^ 8 := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left (by omega) 8
    have hpoly : (y + 1) ^ 8 ≤ 2 * y ^ 8 := by
      have h28 : (28 : ℕ) ^ 8 ≤ 2 * 27 ^ 8 := by norm_num
      have hbig : 27 ^ 8 * (y + 1) ^ 8 ≤ 27 ^ 8 * (2 * y ^ 8) := by
        calc 27 ^ 8 * (y + 1) ^ 8 ≤ 28 ^ 8 * y ^ 8 := hpow
          _ ≤ (2 * 27 ^ 8) * y ^ 8 := Nat.mul_le_mul_right _ h28
          _ = 27 ^ 8 * (2 * y ^ 8) := by ring
      exact Nat.le_of_mul_le_mul_left hbig (by norm_num)
    have h2 : 40 * (y + 1) ^ 8 ≤ 2 * (40 * y ^ 8) := by
      linarith [hpoly]
    rw [pow_succ 4 y]
    linarith [ih, h2, Nat.zero_le (4 ^ y)]

private theorem mul_le_div_pow_succ {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    p * ((p ^ a - 1) / (p - 1)) ≤ (p ^ (a + 1) - 1) / (p - 1) := by
  apply (Nat.le_div_iff_mul_le (by omega)).2
  have hX : 1 ≤ p ^ a := Nat.one_le_pow _ _ (by omega)
  have hY : (p ^ a - 1) / (p - 1) * (p - 1) ≤ p ^ a - 1 := Nat.div_mul_le_self _ _
  rw [pow_succ' p a]
  generalize p ^ a = X at hX hY ⊢
  generalize (X - 1) / (p - 1) = Y at hY ⊢
  have h1 : Y * (p - 1) + 1 ≤ X := (Nat.le_sub_iff_add_le hX).1 hY
  have h3 : p * (Y * (p - 1) + 1) ≤ p * X := Nat.mul_le_mul_left p h1
  apply Nat.le_sub_of_add_le
  nlinarith [h3]

private theorem pow_three_le_div_pow_four (p : ℕ) (hp : 3 ≤ p) :
    p ^ 3 ≤ (p ^ 4 - 1) / (p - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  apply (Nat.le_div_iff_mul_le (by omega)).2
  rw [Nat.add_sub_cancel]
  apply Nat.le_sub_of_add_le
  have h : (s + 1) ^ 4 = (s + 1) ^ 3 * s + (s + 1) ^ 3 := by ring
  have : 1 ≤ (s + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  rw [h]
  linarith

private theorem step_poly_le {p a : ℕ} (hp : 3 ≤ p) (ha : 4 ≤ a) :
    2 * (a + 1) * (a + 2) * p ^ ((a + 1) * (a + 3)) ≤
      (2 * a * (a + 1) * p ^ (a * (a + 2))) ^ p := by
  have hL : (2 * a * (a + 1) * p ^ (a * (a + 2))) ^ p =
      (2 * a * (a + 1)) ^ p * p ^ (a * (a + 2) * p) := by
    rw [mul_pow, ← pow_mul]
  have hc : a + 2 ≤ 2 * a * (a + 1) := by nlinarith
  have hc2 : 2 * (a + 1) ≤ 2 * a * (a + 1) := by nlinarith
  have hi : 2 * (a + 1) * (a + 2) ≤ (2 * a * (a + 1)) ^ p := by
    calc 2 * (a + 1) * (a + 2) ≤ (2 * a * (a + 1)) * (2 * a * (a + 1)) :=
          Nat.mul_le_mul hc2 hc
      _ = (2 * a * (a + 1)) ^ 2 := by ring
      _ ≤ (2 * a * (a + 1)) ^ p := Nat.pow_le_pow_right (by omega) (by omega)
  have hii : p ^ ((a + 1) * (a + 3)) ≤ p ^ (a * (a + 2) * p) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  rw [hL]
  exact Nat.mul_le_mul hi hii

private theorem two_mul_mul_pow_lt_four_pow {p : ℕ} (hp : 3 ≤ p) {a : ℕ} (ha : 4 ≤ a) :
    2 * a * (a + 1) * p ^ (a * (a + 2)) < 4 ^ ((p ^ a - 1) / (p - 1)) := by
  induction a, ha using Nat.le_induction with
  | base =>
    have h1 : 2 * 4 * (4 + 1) * p ^ (4 * (4 + 2)) = 40 * (p ^ 3) ^ 8 := by ring
    rw [h1]
    have h27 : 27 ≤ p ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp 3
    exact lt_of_lt_of_le (forty_mul_pow_eight_lt_four_pow h27)
      (Nat.pow_le_pow_right (by norm_num) (pow_three_le_div_pow_four p hp))
  | succ a ha ih =>
    have hm : p * ((p ^ a - 1) / (p - 1)) ≤ (p ^ (a + 1) - 1) / (p - 1) :=
      mul_le_div_pow_succ (by omega) a
    have h4 : (4 ^ ((p ^ a - 1) / (p - 1))) ^ p ≤ 4 ^ ((p ^ (a + 1) - 1) / (p - 1)) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hm)
    have h5 : (2 * a * (a + 1) * p ^ (a * (a + 2))) ^ p <
        (4 ^ ((p ^ a - 1) / (p - 1))) ^ p :=
      Nat.pow_lt_pow_left ih (by omega)
    calc 2 * (a + 1) * (a + 2) * p ^ ((a + 1) * (a + 3))
        ≤ (2 * a * (a + 1) * p ^ (a * (a + 2))) ^ p := step_poly_le hp ha
      _ < (4 ^ ((p ^ a - 1) / (p - 1))) ^ p := h5
      _ ≤ 4 ^ ((p ^ (a + 1) - 1) / (p - 1)) := h4

private theorem pow_two_le_div_pow_three (p : ℕ) (hp : 3 ≤ p) :
    p ^ 2 ≤ (p ^ 3 - 1) / (p - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  apply (Nat.le_div_iff_mul_le (by omega)).2
  rw [Nat.add_sub_cancel]
  apply Nat.le_sub_of_add_le
  have h : (s + 1) ^ 3 = (s + 1) ^ 2 * s + (s + 1) ^ 2 := by ring
  have : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [h]
  linarith

theorem card_aut_psln_lt {p e n z : ℕ} (hp : 3 ≤ p) (hn : 3 ≤ n) (he : 1 ≤ e)
    (h31 : ¬ (n = 3 ∧ e = 1)) (hz : Odd z) (hzn : z ∣ n) :
    z * (p ^ (e * (n ^ 2 - 1)) * e * 2) < (p + 1) ^ ((p ^ (e * (n - 1)) - 1) / (p - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hkn : k + 1 - 1 = k := by omega
  have hsq : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    rw [this, Nat.add_sub_cancel]
  rw [hkn, hsq]
  have hM4 : 4 ^ ((p ^ (e * k) - 1) / (p - 1)) ≤ (p + 1) ^ ((p ^ (e * k) - 1) / (p - 1)) :=
    Nat.pow_le_pow_left (by omega) _
  refine lt_of_lt_of_le ?_ hM4
  have hek_ge : k ≤ e * k := by nlinarith
  rcases Nat.lt_or_ge (e * k) 4 with hsmall | hbig
  ·
    have he1 : e = 1 := by
      rcases Nat.lt_or_ge e 2 with h | h
      · omega
      · nlinarith
    subst he1
    have hk4 : k < 4 := by linarith
    have hk : k = 2 ∨ k = 3 := by omega
    rcases hk with rfl | rfl
    · exact absurd ⟨by norm_num, rfl⟩ h31
    · have hz1 : z = 1 := by
        have hzle : z ≤ 3 + 1 := Nat.le_of_dvd (by norm_num) hzn
        interval_cases z <;> first | rfl | exact absurd hz (by decide) | exact absurd hzn (by decide)
      subst hz1
      by_cases hp5 : p ≤ 5
      · interval_cases p <;> norm_num
      · have hM : p ^ 2 ≤ (p ^ (1 * 3) - 1) / (p - 1) := by
          rw [one_mul]
          exact pow_two_le_div_pow_three p hp
        have hA : p ^ (1 * (3 * (3 + 2))) ≤ (p ^ 2) ^ 8 := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (by omega) (by norm_num)
        have hy : 27 ≤ p ^ 2 := by nlinarith
        have hB : 40 * (p ^ 2) ^ 8 < 4 ^ (p ^ 2) := forty_mul_pow_eight_lt_four_pow hy
        have hC : 4 ^ (p ^ 2) ≤ 4 ^ ((p ^ (1 * 3) - 1) / (p - 1)) :=
          Nat.pow_le_pow_right (by norm_num) hM
        calc 1 * (p ^ (1 * (3 * (3 + 2))) * 1 * 2) ≤ 2 * (p ^ 2) ^ 8 := by
              have := Nat.mul_le_mul_right (2 : ℕ) hA
              linarith
          _ < 4 ^ (p ^ 2) := by linarith [hB, Nat.zero_le ((p ^ 2) ^ 8)]
          _ ≤ 4 ^ ((p ^ (1 * 3) - 1) / (p - 1)) := hC
  ·
    have hz_le : z ≤ k + 1 := Nat.le_of_dvd (by omega) hzn
    have hzA : z ≤ e * k + 1 := by linarith
    have heA : e ≤ e * k := by nlinarith
    have hE : e * (k * (k + 2)) ≤ (e * k) * ((e * k) + 2) := by
      calc e * (k * (k + 2)) = (e * k) * (k + 2) := by ring
        _ ≤ (e * k) * ((e * k) + 2) := Nat.mul_le_mul_left _ (by linarith)
    have hpE : p ^ (e * (k * (k + 2))) ≤ p ^ ((e * k) * ((e * k) + 2)) :=
      Nat.pow_le_pow_right (by omega) hE
    calc z * (p ^ (e * (k * (k + 2))) * e * 2)
        ≤ (e * k + 1) * (p ^ ((e * k) * ((e * k) + 2)) * (e * k) * 2) := by gcongr
      _ = 2 * (e * k) * (e * k + 1) * p ^ ((e * k) * ((e * k) + 2)) := by ring
      _ < 4 ^ ((p ^ (e * k) - 1) / (p - 1)) := two_mul_mul_pow_lt_four_pow hp hbig

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
