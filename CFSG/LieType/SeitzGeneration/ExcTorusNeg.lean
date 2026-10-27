module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LieType.SeitzGeneration

theorem neg_one_ne_one_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  exact ZMod.neg_one_ne_one

variable {F : Type*} [Field F] {x : F}

theorem sq_eq_one_cases (y : F) (h : y ^ 2 = 1) : y = 1 ∨ y = -1 := by
  have : (y - 1) * (y + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem neg_pow_cases (x : F) (n : ℕ) :
    ((-x) ^ n = x ^ n ∧ Even n) ∨ ((-x) ^ n = -x ^ n ∧ Odd n) := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl ⟨h.neg_pow x, h⟩
  · exact Or.inr ⟨h.neg_pow x, h⟩

theorem orderOf_neg_of_odd (h1 : (-1 : F) ≠ 1) {e : ℕ} (he : orderOf x = e) (hodd : Odd e)
    (he0 : e ≠ 0) : orderOf (-x) = 2 * e := by
  have hxe : x ^ e = 1 := he ▸ pow_orderOf_eq_one x
  have hpos : 0 < e := Nat.pos_of_ne_zero he0
  have hneg2e : (-x) ^ (2 * e) = 1 := by
    calc (-x) ^ (2 * e) = ((-x) ^ 2) ^ e := pow_mul _ _ _
      _ = (x ^ 2) ^ e := by rw [neg_sq]
      _ = (x ^ e) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [hxe, one_pow]
  have hdvd : orderOf (-x) ∣ 2 * e := orderOf_dvd_of_pow_eq_one hneg2e
  have hn0 : 0 < orderOf (-x) := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2 * e,
    by omega, hneg2e⟩)
  set n := orderOf (-x) with hn
  have hnx : (-x) ^ n = 1 := pow_orderOf_eq_one _
  rcases neg_pow_cases x n with ⟨hn1, hev⟩ | ⟨hn1, hodd'⟩
  ·
    have hxn : x ^ n = 1 := hn1 ▸ hnx
    have hen : e ∣ n := he ▸ orderOf_dvd_of_pow_eq_one hxn
    have h2n : 2 ∣ n := even_iff_two_dvd.1 hev
    have hcop : Nat.Coprime 2 e := Nat.coprime_two_left.2 hodd
    have : 2 * e ∣ n := hcop.mul_dvd_of_dvd_of_dvd h2n hen
    exact Nat.dvd_antisymm hdvd this
  ·
    exfalso
    have hxn : x ^ n = -1 := by
      have : -x ^ n = 1 := hn1 ▸ hnx
      linear_combination -this
    have hx2n : x ^ (2 * n) = 1 := by rw [pow_mul', hxn]; simp
    have he2n : e ∣ 2 * n := he ▸ orderOf_dvd_of_pow_eq_one hx2n
    have hcop : Nat.Coprime e 2 := Nat.coprime_two_right.2 hodd
    have hen : e ∣ n := hcop.dvd_of_dvd_mul_left he2n
    have hen' : orderOf x ∣ n := he ▸ hen
    have : x ^ n = 1 := orderOf_dvd_iff_pow_eq_one.1 hen'
    rw [this] at hxn
    exact h1 hxn.symm

theorem orderOf_neg_of_two_mod_four {e : ℕ} (he : orderOf x = e)
    (h4 : e % 4 = 2) : orderOf (-x) = e / 2 := by
  have hxe : x ^ e = 1 := he ▸ pow_orderOf_eq_one x
  obtain ⟨m, hm⟩ : ∃ m, e = 2 * m ∧ m % 2 = 1 := ⟨e / 2, by omega, by omega⟩
  obtain ⟨rfl, hmodd⟩ := hm
  have hm0 : 0 < m := by omega
  have hmo : Odd m := Nat.odd_iff.2 hmodd
  have hxm : x ^ m = -1 := by
    have hsq : (x ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact hxe
    rcases sq_eq_one_cases _ hsq with h | h
    · exfalso
      have : 2 * m ∣ m := he ▸ orderOf_dvd_of_pow_eq_one h
      have := Nat.le_of_dvd hm0 this
      omega
    · exact h
  have hnegm : (-x) ^ m = 1 := by rw [hmo.neg_pow, hxm]; simp
  have hdvd : orderOf (-x) ∣ m := orderOf_dvd_of_pow_eq_one hnegm
  have hn0 : 0 < orderOf (-x) := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm0, hnegm⟩)
  set n := orderOf (-x) with hn
  have hnodd : Odd n := hmo.of_dvd_nat hdvd
  have hnx : (-x) ^ n = 1 := pow_orderOf_eq_one _
  have hxn : x ^ n = -1 := by
    have : -x ^ n = 1 := by rw [← hnodd.neg_pow]; exact hnx
    linear_combination -this
  have hx2n : x ^ (2 * n) = 1 := by rw [pow_mul', hxn]; simp
  have he2n : 2 * m ∣ 2 * n := he ▸ orderOf_dvd_of_pow_eq_one hx2n
  have hmn : m ∣ n := Nat.dvd_of_mul_dvd_mul_left (by norm_num) he2n
  rw [show 2 * m / 2 = m by omega]
  exact Nat.dvd_antisymm hdvd hmn

theorem orderOf_neg_of_four_dvd {e : ℕ} (he : orderOf x = e) (h4 : 4 ∣ e)
    (he0 : e ≠ 0) : orderOf (-x) = e := by
  have hxe : x ^ e = 1 := he ▸ pow_orderOf_eq_one x
  have hev : Even e := even_iff_two_dvd.2 (dvd_trans (by norm_num) h4)
  have hnege : (-x) ^ e = 1 := by rw [hev.neg_pow, hxe]
  have hdvd : orderOf (-x) ∣ e := orderOf_dvd_of_pow_eq_one hnege
  have hpos : 0 < e := Nat.pos_of_ne_zero he0
  have hn0 : 0 < orderOf (-x) := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨e, hpos, hnege⟩)
  set n := orderOf (-x) with hn
  have hnx : (-x) ^ n = 1 := pow_orderOf_eq_one _
  rcases neg_pow_cases x n with ⟨hn1, hev'⟩ | ⟨hn1, hodd'⟩
  · have hxn : x ^ n = 1 := hn1 ▸ hnx
    have : e ∣ n := he ▸ orderOf_dvd_of_pow_eq_one hxn
    exact Nat.dvd_antisymm hdvd this
  · exfalso
    have hxn : x ^ n = -1 := by
      have : -x ^ n = 1 := hn1 ▸ hnx
      linear_combination -this
    have hx2n : x ^ (2 * n) = 1 := by rw [pow_mul', hxn]; simp
    have he2n : e ∣ 2 * n := he ▸ orderOf_dvd_of_pow_eq_one hx2n
    obtain ⟨c, hc⟩ := h4
    have h2 : 2 * c ∣ n := by
      have : 2 * (2 * c) ∣ 2 * n := by
        have h22 : 2 * (2 * c) = e := by omega
        rw [h22]
        exact he2n
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have : Even n := even_iff_two_dvd.2 (dvd_trans (dvd_mul_right 2 c) h2)
    exact (Nat.not_even_iff_odd.2 hodd') this

end CFSG.LieType.SeitzGeneration
