module

public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Malle.Proving

private lemma fact_three_prime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private lemma one_lt_pow_of_ne {q n : ℕ} (hq : 1 < q) (hn : n ≠ 0) : 1 < q ^ n :=
  calc 1 < q := hq
    _ = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) (by omega)

private lemma sub_one_ne_zero' {q n : ℕ} (hq : 1 < q) (hn : n ≠ 0) : q ^ n - 1 ≠ 0 :=
  (Nat.sub_pos_of_lt (one_lt_pow_of_ne hq hn)).ne'

private lemma sq_sub_one_eq {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

private lemma padicValNat_three_sq_sub_one {q : ℕ} (hq : 1 < q) (h3 : q % 3 = 2) :
    padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) := by
  have := fact_three_prime
  rw [sq_sub_one_eq (by omega : 1 ≤ q),
    padicValNat.mul (by omega : q + 1 ≠ 0) (by omega : q - 1 ≠ 0),
    padicValNat.eq_zero_of_not_dvd (by omega : ¬ 3 ∣ q - 1), add_zero]

private lemma padicValNat_three_pow_sub_one {q : ℕ} (hq : 1 < q) (h3 : q % 3 = 2) {d : ℕ}
    (hd : d ≠ 0) (he : 2 ∣ d) :
    padicValNat 3 (q ^ d - 1) = padicValNat 3 (q + 1) + padicValNat 3 (d / 2) := by
  have := fact_three_prime
  obtain ⟨m, rfl⟩ := he
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hd
  have hd2 : 2 * m / 2 = m := by omega
  have hyx : (1 : ℕ) < q ^ 2 := by nlinarith
  have hxy : 3 ∣ q ^ 2 - 1 := by
    rw [sq_sub_one_eq (by omega : 1 ≤ q)]
    exact Dvd.dvd.mul_right (by omega : 3 ∣ q + 1) _
  have hx : ¬ 3 ∣ q ^ 2 := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have key : q ^ (2 * m) - 1 = (q ^ 2) ^ m - 1 ^ m := by rw [one_pow, pow_mul]
  rw [hd2, key, padicValNat.pow_sub_pow (by decide : Odd 3) hyx hxy hx hm,
    padicValNat_three_sq_sub_one hq h3]

private lemma v3_block {q : ℕ} (hq : 1 < q) (h3 : q % 3 = 2) {d e : ℕ}
    (hd : d ≠ 0) (he : 2 ∣ d) (hde : d / 2 = e) :
    padicValNat 3 (q ^ d - 1) = padicValNat 3 (q + 1) + padicValNat 3 e := by
  rw [padicValNat_three_pow_sub_one hq h3 hd he, hde]

private lemma v3_pow_eq_zero {q : ℕ} (h3 : q % 3 = 2) (n : ℕ) :
    padicValNat 3 (q ^ n) = 0 := by
  have := fact_three_prime
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

private lemma v3_one : padicValNat 3 1 = 0 := by simp

private lemma v3_three : padicValNat 3 3 = 1 := by
  have := fact_three_prime
  simp

private lemma v3_four : padicValNat 3 4 = 0 := by
  have := fact_three_prime
  exact padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma v3_six : padicValNat 3 6 = 1 := by
  have := fact_three_prime
  have h : padicValNat 3 (3 * 2) = padicValNat 3 3 + padicValNat 3 2 :=
    padicValNat.mul (by norm_num) (by norm_num)
  rw [v3_three, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), add_zero] at h
  simpa using h

theorem padicValNat_three_ordF4_of_mod_two {q : ℕ}
    (hq : 1 < q) (h3 : q % 3 = 2) :
    padicValNat 3 (CFSG.Open.ordF4 q) = 4 * padicValNat 3 (q + 1) + 2 := by
  have := fact_three_prime
  have n24 : q ^ 24 ≠ 0 := pow_ne_zero _ (by omega)
  have n12 : q ^ 12 - 1 ≠ 0 := sub_one_ne_zero' hq (by norm_num)
  have n8 : q ^ 8 - 1 ≠ 0 := sub_one_ne_zero' hq (by norm_num)
  have n6 : q ^ 6 - 1 ≠ 0 := sub_one_ne_zero' hq (by norm_num)
  have n2 : q ^ 2 - 1 ≠ 0 := sub_one_ne_zero' hq (by norm_num)
  have b12 : padicValNat 3 (q ^ 12 - 1) = padicValNat 3 (q + 1) + 1 := by
    rw [v3_block hq h3 (d := 12) (e := 6) (by norm_num) (by norm_num) (by norm_num), v3_six]
  have b8 : padicValNat 3 (q ^ 8 - 1) = padicValNat 3 (q + 1) + 0 := by
    rw [v3_block hq h3 (d := 8) (e := 4) (by norm_num) (by norm_num) (by norm_num), v3_four]
  have b6 : padicValNat 3 (q ^ 6 - 1) = padicValNat 3 (q + 1) + 1 := by
    rw [v3_block hq h3 (d := 6) (e := 3) (by norm_num) (by norm_num) (by norm_num), v3_three]
  have b2 : padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) + 0 := by
    rw [v3_block hq h3 (d := 2) (e := 1) (by norm_num) (by norm_num) (by norm_num), v3_one]
  unfold CFSG.Open.ordF4
  rw [padicValNat.mul, padicValNat.mul, padicValNat.mul, padicValNat.mul,
    v3_pow_eq_zero h3 24, b12, b8, b6, b2]
  · omega
  all_goals (repeat' (first | assumption | apply mul_ne_zero))

end CFSG.HardMathSupport.Malle.Proving

end
