module

public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Open

private lemma fact_three_prime' : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private lemma sq_sub_one_eq' {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

private lemma v3_sq_sub_one' {q : ℕ} (hq : 1 < q) (h3 : q % 3 = 2) :
    padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) := by
  have := fact_three_prime'
  rw [sq_sub_one_eq' (by omega : 1 ≤ q),
    padicValNat.mul (by omega : q + 1 ≠ 0) (by omega : q - 1 ≠ 0),
    padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ q - 1), add_zero]

private lemma v3_pow_sub_one' {q : ℕ} (hq : 1 < q) (h3 : q % 3 = 2) {d : ℕ}
    (hd : d ≠ 0) (he : 2 ∣ d) :
    padicValNat 3 (q ^ d - 1) = padicValNat 3 (q + 1) + padicValNat 3 (d / 2) := by
  have := fact_three_prime'
  obtain ⟨m, rfl⟩ := he
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hd
  have hd2 : 2 * m / 2 = m := by omega
  have hyx : (1 : ℕ) < q ^ 2 := by nlinarith
  have hxy : 3 ∣ q ^ 2 - 1 := by
    rw [sq_sub_one_eq' (by omega : 1 ≤ q)]
    exact Dvd.dvd.mul_right (by omega : 3 ∣ q + 1) _
  have hx : ¬ 3 ∣ q ^ 2 := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have key : q ^ (2 * m) - 1 = (q ^ 2) ^ m - 1 ^ m := by rw [one_pow, pow_mul]
  rw [hd2, key, padicValNat.pow_sub_pow (by decide : Odd 3) hyx hxy hx hm,
    v3_sq_sub_one' hq h3]

private lemma v3_pow_add_one' {q : ℕ} (hq : 1 < q) (h3 : q % 3 = 2) {d : ℕ} (hd : Odd d) :
    padicValNat 3 (q ^ d + 1) = padicValNat 3 (q + 1) + padicValNat 3 d := by
  have := fact_three_prime'
  have hx : ¬ 3 ∣ q := by omega
  have key : q ^ d + 1 = q ^ d + 1 ^ d := by rw [one_pow]
  rw [key, padicValNat.pow_add_pow (by decide : Odd 3) (by omega : 3 ∣ q + 1) hx hd]

theorem padicValNat_three_ordTwistedE6_of_mod_two {q : ℕ} (hq : 1 < q) (hq3 : q % 3 = 2) :
    padicValNat 3 (ordTwistedE6 q) = 6 * padicValNat 3 (q + 1) + 3 := by
  have := fact_three_prime'
  have hgcd : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left (by omega)
  have hnz : ∀ n, n ≠ 0 → q ^ n - 1 ≠ 0 := fun n hn =>
    (Nat.sub_pos_of_lt (Nat.one_lt_pow hn hq)).ne'
  have hne : ∀ n, q ^ n + 1 ≠ 0 := fun n => Nat.succ_ne_zero _
  have h36 : q ^ 36 ≠ 0 := pow_ne_zero _ (by omega)
  have h12 := hnz 12 (by norm_num)
  have h8 := hnz 8 (by norm_num)
  have h6 := hnz 6 (by norm_num)
  have h2' := hnz 2 (by norm_num)
  have h9 := hne 9
  have h5 := hne 5
  have e3 : padicValNat 3 3 = 1 := padicValNat_self
  have e6 : padicValNat 3 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num), e3,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
  have e4 : padicValNat 3 4 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have e9 : padicValNat 3 9 = 2 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, padicValNat.prime_pow]
  have e5 : padicValNat 3 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have e1 : padicValNat 3 1 = 0 := by simp
  have A1 := mul_ne_zero h36 h12
  have A2 := mul_ne_zero A1 h9
  have A3 := mul_ne_zero A2 h8
  have A4 := mul_ne_zero A3 h6
  have A5 := mul_ne_zero A4 h5
  have hnum3 : 3 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    rw [sq_sub_one_eq' (by omega : 1 ≤ q)]
    exact Dvd.dvd.mul_right (by omega : 3 ∣ q + 1) _
  unfold ordTwistedE6
  rw [hgcd, padicValNat.div_of_dvd hnum3, e3]
  rw [padicValNat.mul A5 h2', padicValNat.mul A4 h5, padicValNat.mul A3 h6,
    padicValNat.mul A2 h8, padicValNat.mul A1 h9, padicValNat.mul h36 h12,
    padicValNat.pow q 36, padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ q),
    v3_pow_sub_one' hq hq3 (by norm_num : 12 ≠ 0) (by norm_num),
    v3_pow_sub_one' hq hq3 (by norm_num : 8 ≠ 0) (by norm_num),
    v3_pow_sub_one' hq hq3 (by norm_num : 6 ≠ 0) (by norm_num),
    v3_pow_sub_one' hq hq3 (by norm_num : 2 ≠ 0) (by norm_num),
    v3_pow_add_one' hq hq3 (by decide : Odd 9), v3_pow_add_one' hq hq3 (by decide : Odd 5)]
  norm_num [e6, e4, e9, e5, e1]
  omega

end CFSG.HardMathSupport.Malle.E27Lie
