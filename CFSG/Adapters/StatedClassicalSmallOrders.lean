module

public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Open.StatedAPI

variable {X : Type} [Group X]

theorem card_of_statedClassicalModel_psl_three_two (h : StatedClassicalModel X .PSL 3 2 1) :
    Nat.card X = 168 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_four_two (h : StatedClassicalModel X .PSL 4 2 1) :
    Nat.card X = 20160 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_three_four (h : StatedClassicalModel X .PSL 3 2 2) :
    Nat.card X = 20160 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_three_three (h : StatedClassicalModel X .PSL 3 3 1) :
    Nat.card X = 5616 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_two_seven (h : StatedClassicalModel X .PSL 2 7 1) :
    Nat.card X = 168 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_five_two (h : StatedClassicalModel X .PSL 5 2 1) :
    Nat.card X = 9999360 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_three_five (h : StatedClassicalModel X .PSL 3 5 1) :
    Nat.card X = 372000 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_two_four (h : StatedClassicalModel X .PSL 2 2 2) :
    Nat.card X = 60 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_two_forty_nine (h : StatedClassicalModel X .PSL 2 7 2) :
    Nat.card X = 58800 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_two_eight (h : StatedClassicalModel X .PSL 2 2 3) :
    Nat.card X = 504 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_two_five (h : StatedClassicalModel X .PSL 2 5 1) :
    Nat.card X = 60 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_two_twenty_five (h : StatedClassicalModel X .PSL 2 5 2) :
    Nat.card X = 7800 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_two_nine (h : StatedClassicalModel X .PSL 2 3 2) :
    Nat.card X = 360 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_three_seven (h : StatedClassicalModel X .PSL 3 7 1) :
    Nat.card X = 1876896 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_three_nine (h : StatedClassicalModel X .PSL 3 3 2) :
    Nat.card X = 42456960 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_three_sixteen (h : StatedClassicalModel X .PSL 3 2 4) :
    Nat.card X = 1425715200 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_four_four (h : StatedClassicalModel X .PSL 4 2 2) :
    Nat.card X = 987033600 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_four_three (h : StatedClassicalModel X .PSL 4 3 1) :
    Nat.card X = 6065280 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psl_two_sixteen (h : StatedClassicalModel X .PSL 2 2 4) :
    Nat.card X = 4080 := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  decide

theorem two_mul_card_of_statedClassicalModel_psl_two_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : StatedClassicalModel X .PSL 2 p 1) : 2 * Nat.card X = p * (p ^ 2 - 1) := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
  rw [hg]
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton]
  have h2 : 2 ∣ p * (p ^ 2 - 1) :=
    dvd_mul_of_dvd_right (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _
  exact Nat.mul_div_cancel' h2

theorem card_mul_two_of_statedClassicalModel_psl_two_odd {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : StatedClassicalModel X .PSL 2 p e) : Nat.card X * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hg : Nat.gcd 2 (p ^ e - 1) = 2 :=
    Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
  rw [hg]
  simp only [show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one, Finset.Icc_self,
    Finset.prod_singleton]
  have h2 : 2 ∣ p ^ e * ((p ^ e) ^ 2 - 1) :=
    dvd_mul_of_dvd_right (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _
  exact Nat.div_mul_cancel h2

theorem card_of_statedClassicalModel_psl_two_two {n : ℕ} (h : StatedClassicalModel X .PSL 2 2 n) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [card_of_statedClassicalModel_psl (by norm_num) h]
  have hn1 : 1 ≤ n := h.1.2.1
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨k, hk⟩ : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn1)
    exact ⟨k - 1, by omega⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp (Nat.coprime_two_right.mpr hodd)),
    Nat.div_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self, Finset.prod_singleton,
    pow_one]

theorem three_dvd_card_of_statedClassicalModel_psl_two_two {n : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 n) : 3 ∣ Nat.card X := by
  rw [card_of_statedClassicalModel_psl_two_two h, ← pow_mul, mul_comm n 2, pow_mul]
  refine Dvd.dvd.mul_left ?_ _
  exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) n

end CFSG.Open.StatedAPI

namespace CFSG.Blueprint

theorem LieModel.card_psl_three_two {Y : Type} [Group Y] (h : LieModel Y .PSL 3 2 1) :
    Nat.card Y = 168 :=
  Open.StatedAPI.card_of_statedClassicalModel_psl_three_two (h.statedClassicalModel (by decide))

end CFSG.Blueprint
