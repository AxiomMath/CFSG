module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddBase
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Open

theorem gomiOdd_two_pow_nine_dvd_ordBC {n q : ℕ} (hq : Odd q) (hn : 3 ≤ n) :
    2 ^ 9 ∣ ordBC n q := by
  unfold ordBC
  have h8 : 8 ∣ q ^ 2 - 1 := gomiOdd_eight_dvd_sq_sub_one hq
  have h16 : 16 ∣ q ^ 4 - 1 := gomiOdd_sixteen_dvd_pow_four_sub_one hq
  have h8' : 8 ∣ q ^ 6 - 1 := h8.trans (by simpa using gomiOdd_sq_sub_one_dvd_pow_two_mul q 3)
  have hprod : (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) ∣
      ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
    have hsub : Finset.Icc 1 3 ⊆ Finset.Icc 1 n := Finset.Icc_subset_Icc le_rfl hn
    have := Finset.prod_dvd_prod_of_subset (Finset.Icc 1 3) (Finset.Icc 1 n)
      (fun i => q ^ (2 * i) - 1) hsub
    simpa [Finset.prod_Icc_succ_top, mul_assoc] using this
  have h2 : 2 ^ 10 ∣ q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
    refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ hprod) _
    have : 8 * 16 * 8 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
      mul_dvd_mul (mul_dvd_mul h8 h16) h8'
    exact this
  have hg : Nat.gcd 2 (q - 1) ∣ 2 ^ 1 := by simpa using Nat.gcd_dvd_left 2 (q - 1)
  exact gomiOdd_pow_dvd_div_of_dvd_two_pow hg (by simpa using h2)

theorem gomiOddB_prod5 (q : ℕ) : ∏ i ∈ Finset.Icc 2 5, (q ^ i - 1) =
    (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1) := by
  simp [Finset.prod_Icc_succ_top, mul_assoc]

theorem gomiOddB_prod6 (q : ℕ) : ∏ i ∈ Finset.Icc 2 6, (q ^ i - 1) =
    (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1) * (q ^ 6 - 1) := by
  simp [Finset.prod_Icc_succ_top, mul_assoc]

theorem gomiOdd_two_pow_nine_dvd_ordA_four {q : ℕ} (hq : Odd q) : 2 ^ 9 ∣ ordA 4 q := by
  have h8 := gomiOdd_eight_dvd_sq_sub_one hq
  have h16 := gomiOdd_sixteen_dvd_pow_four_sub_one hq
  have h3 := gomiOdd_two_dvd_pow_sub_one hq 3
  have h5 := gomiOdd_two_dvd_pow_sub_one hq 5
  have hprod : ∏ i ∈ Finset.Icc 2 (4 + 1), (q ^ i - 1) =
      (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1) := gomiOddB_prod5 q
  unfold ordA
  rw [hprod]
  have hgodd : Odd (Nat.gcd (4 + 1) (q - 1)) :=
    Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left (4 + 1) (q - 1))
  have hgX : Nat.gcd (4 + 1) (q - 1) ∣
      q ^ (4 * (4 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)) :=
    ((Nat.gcd_dvd_right (4 + 1) (q - 1)).trans (gomiOdd_sub_one_dvd_pow_sub_one q 2)).trans
      ⟨q ^ (4 * (4 + 1) / 2) * ((q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)), by ring⟩
  refine gomiOdd_pow_dvd_div_of_odd hgX hgodd ?_
  refine Dvd.dvd.mul_left ?_ _
  have : 8 * 2 * 16 * 2 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1) :=
    mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h8 h3) h16) h5
  exact Dvd.dvd.trans (by norm_num) this

theorem gomiOdd_two_pow_nine_dvd_ordA_ge {n q : ℕ} (hq : Odd q) (hn : 5 ≤ n) :
    2 ^ 9 ∣ ordA n q := by
  have h8 := gomiOdd_eight_dvd_sq_sub_one hq
  have h16 := gomiOdd_sixteen_dvd_pow_four_sub_one hq
  have h5 := gomiOdd_two_dvd_pow_sub_one hq 5
  have h6 : 8 ∣ q ^ 6 - 1 := h8.trans (by simpa using gomiOdd_sq_sub_one_dvd_pow_two_mul q 3)
  unfold ordA
  have hsub : Finset.Icc 2 6 ⊆ Finset.Icc 2 (n + 1) := Finset.Icc_subset_Icc le_rfl (by omega)
  obtain ⟨R, hR⟩ := Finset.prod_dvd_prod_of_subset (Finset.Icc 2 6) (Finset.Icc 2 (n + 1))
    (fun i => q ^ i - 1) hsub
  rw [gomiOddB_prod6] at hR
  obtain ⟨u, hu⟩ := gomiOdd_sub_one_dvd_pow_sub_one q 3
  obtain ⟨h, hh⟩ : Nat.gcd (n + 1) (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
  have hgpos : 0 < Nat.gcd (n + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  set g := Nat.gcd (n + 1) (q - 1) with hg
  set W : ℕ := q ^ (n * (n + 1) / 2) * ((q ^ 2 - 1) * u * (q ^ 4 - 1) * (q ^ 5 - 1) *
    (q ^ 6 - 1) * R) with hW
  have hX : q ^ (n * (n + 1) / 2) * ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) = g * (h * W) := by
    rw [hR, hu, hW]
    have : q - 1 = g * h := hh
    rw [this]
    ring
  rw [hX, Nat.mul_div_cancel_left _ hgpos]
  refine Dvd.dvd.mul_left ?_ _
  have hdiv : 8 * 16 * 2 * 8 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1) * (q ^ 6 - 1) :=
    mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h8 h16) h5) h6
  have hW2 : (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1) * (q ^ 6 - 1) ∣ W :=
    ⟨q ^ (n * (n + 1) / 2) * u * R, by rw [hW]; ring⟩
  exact Dvd.dvd.trans (by norm_num) (hdiv.trans hW2)

theorem gomiOdd_two_pow_nine_dvd_ordA {n q : ℕ} (hq : Odd q) (hn : 4 ≤ n) :
    2 ^ 9 ∣ ordA n q := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · exact gomiOdd_two_pow_nine_dvd_ordA_four hq
  · exact gomiOdd_two_pow_nine_dvd_ordA_ge hq hn5

theorem gomiOddB_natCast_pow_toNat (q i : ℕ) : ((q : ℤ) ^ i).toNat = q ^ i := by
  exact_mod_cast Int.toNat_natCast (q ^ i)

theorem gomiOddB_natCast_pow_add_one_toNat (q i : ℕ) :
    ((q : ℤ) ^ i + 1).toNat = q ^ i + 1 := by
  exact_mod_cast Int.toNat_natCast (q ^ i + 1)

theorem gomiOddB_prodU5 (q : ℕ) :
    ∏ i ∈ Finset.Icc 2 5, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat =
      (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) := by
  simp [Finset.prod_Icc_succ_top, gomiOddB_natCast_pow_toNat, gomiOddB_natCast_pow_add_one_toNat]

theorem gomiOddB_prodU6 (q : ℕ) :
    ∏ i ∈ Finset.Icc 2 6, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat =
      (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) * (q ^ 6 - 1) := by
  simp [Finset.prod_Icc_succ_top, gomiOddB_natCast_pow_toNat, gomiOddB_natCast_pow_add_one_toNat]

theorem gomiOdd_two_pow_nine_dvd_ordTwistedA_four {q : ℕ} (hq : Odd q) :
    2 ^ 9 ∣ ordTwistedA 4 q := by
  have h8 := gomiOdd_eight_dvd_sq_sub_one hq
  have h16 := gomiOdd_sixteen_dvd_pow_four_sub_one hq
  have h3 := gomiOdd_two_dvd_pow_add_one hq 3
  have h5 := gomiOdd_two_dvd_pow_add_one hq 5
  have hprod : ∏ i ∈ Finset.Icc 2 (4 + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat =
      (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) := gomiOddB_prodU5 q
  unfold ordTwistedA
  rw [hprod]
  have hgodd : Odd (Nat.gcd (4 + 1) (q + 1)) :=
    Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left (4 + 1) (q + 1))
  have hgX : Nat.gcd (4 + 1) (q + 1) ∣
      q ^ (4 * (4 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) :=
    ((Nat.gcd_dvd_right (4 + 1) (q + 1)).trans
      (gomiOdd_add_one_dvd_pow_add_one q (by decide : Odd 3))).trans
      ⟨q ^ (4 * (4 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 5 + 1)), by ring⟩
  refine gomiOdd_pow_dvd_div_of_odd hgX hgodd ?_
  refine Dvd.dvd.mul_left ?_ _
  have : 8 * 2 * 16 * 2 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) :=
    mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h8 h3) h16) h5
  exact Dvd.dvd.trans (by norm_num) this

theorem gomiOdd_two_pow_nine_dvd_ordTwistedA_ge {n q : ℕ} (hq : Odd q) (hn : 5 ≤ n) :
    2 ^ 9 ∣ ordTwistedA n q := by
  have h8 := gomiOdd_eight_dvd_sq_sub_one hq
  have h16 := gomiOdd_sixteen_dvd_pow_four_sub_one hq
  have h5 := gomiOdd_two_dvd_pow_add_one hq 5
  have h6 : 8 ∣ q ^ 6 - 1 := h8.trans (by simpa using gomiOdd_sq_sub_one_dvd_pow_two_mul q 3)
  unfold ordTwistedA
  have hsub : Finset.Icc 2 6 ⊆ Finset.Icc 2 (n + 1) := Finset.Icc_subset_Icc le_rfl (by omega)
  obtain ⟨R, hR⟩ := Finset.prod_dvd_prod_of_subset (Finset.Icc 2 6) (Finset.Icc 2 (n + 1))
    (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) hsub
  rw [gomiOddB_prodU6] at hR
  obtain ⟨u, hu⟩ := gomiOdd_add_one_dvd_pow_add_one q (by decide : Odd 3)
  obtain ⟨h, hh⟩ : Nat.gcd (n + 1) (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
  have hgpos : 0 < Nat.gcd (n + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  set g := Nat.gcd (n + 1) (q + 1) with hg
  set W : ℕ := q ^ (n * (n + 1) / 2) * ((q ^ 2 - 1) * u * (q ^ 4 - 1) * (q ^ 5 + 1) *
    (q ^ 6 - 1) * R) with hW
  have hX : q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (n + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = g * (h * W) := by
    rw [hR, hu, hW]
    have : q + 1 = g * h := hh
    rw [this]
    ring
  rw [hX, Nat.mul_div_cancel_left _ hgpos]
  refine Dvd.dvd.mul_left ?_ _
  have hdiv : 8 * 16 * 2 * 8 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 5 + 1) * (q ^ 6 - 1) :=
    mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h8 h16) h5) h6
  have hW2 : (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 5 + 1) * (q ^ 6 - 1) ∣ W :=
    ⟨q ^ (n * (n + 1) / 2) * u * R, by rw [hW]; ring⟩
  exact Dvd.dvd.trans (by norm_num) (hdiv.trans hW2)

theorem gomiOdd_two_pow_nine_dvd_ordTwistedA {n q : ℕ} (hq : Odd q) (hn : 4 ≤ n) :
    2 ^ 9 ∣ ordTwistedA n q := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · exact gomiOdd_two_pow_nine_dvd_ordTwistedA_four hq
  · exact gomiOdd_two_pow_nine_dvd_ordTwistedA_ge hq hn5

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
