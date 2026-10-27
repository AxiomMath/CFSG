module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.LocalAnalysis.ComponentClassification.LieOrderTwoAdic

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.RankThree.PartTwo.KFacts.OddChar

variable {t : StatedLieTag} {n p f N q : ℕ}

theorem odd_pow_of_admissible (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2) :
    Odd (p ^ f) :=
  (hadm.1.eq_two_or_odd'.resolve_left hp2).pow

theorem one_lt_pow_of_admissible (hadm : StatedLieAdmissible t n p f) : 1 < p ^ f :=
  Nat.one_lt_pow (by have := hadm.2.1; omega) hadm.1.one_lt

theorem factorization_two_of_order (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f)) :
    N.factorization 2 + padicValNat 2 (lieOrderDivisor t n (p ^ f)) =
      padicValNat 2 (lieOrderCofactor t n (p ^ f)) := by
  have hq := odd_pow_of_admissible hadm hp2
  have hc := lieOrderCofactor_ne_zero hadm
  have hd := lieOrderDivisor_ne_zero hadm
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_mul, lieOrderNumerator_eq hadm] at hN
    exact mul_ne_zero (pow_ne_zero _ hq.pos.ne') hc hN.symm
  have h := congrArg (padicValNat 2) hN
  rw [padicValNat.mul hN0 hd, lieOrderNumerator_eq hadm, padicValNat_odd_pow_mul hq _ hc] at h
  rwa [Nat.factorization_def _ Nat.prime_two]

theorem padicValNat_lieOrderCofactor_psl_four (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (lieOrderCofactor .PSL 4 q) =
      3 * padicValNat 2 (q - 1) + 2 * padicValNat 2 (q + 1) + 1 := by
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h3 : q ^ 3 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have hc : lieOrderCofactor .PSL 4 q = (q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)) := by
    simp only [lieOrderCofactor]
    rw [show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
      Finset.prod_pair (by decide)]
  rw [hc, padicValNat.mul h2 (mul_ne_zero h3 h4), padicValNat.mul h3 h4,
    padicValNat_pow_four_sub_one hq hq1, padicValNat_pow_three_sub_one hq hq1,
    padicValNat_sq_sub_one hq hq1]
  omega

theorem padicValNat_lieOrderCofactor_psu_four (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (lieOrderCofactor .PSU 4 q) =
      2 * padicValNat 2 (q - 1) + 3 * padicValNat 2 (q + 1) + 1 := by
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h3 : q ^ 3 + 1 ≠ 0 := Nat.succ_ne_zero _
  have h4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have hc : lieOrderCofactor .PSU 4 q = (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) := by
    simp only [lieOrderCofactor]
    rw [show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
      Finset.prod_pair (by decide)]
    simp [Nat.even_iff]
  rw [hc, padicValNat.mul h2 (mul_ne_zero h3 h4), padicValNat.mul h3 h4,
    padicValNat_pow_four_sub_one hq hq1, padicValNat_pow_three_add_one hq,
    padicValNat_sq_sub_one hq hq1]
  omega

theorem padicValNat_lieOrderCofactor_psp_two (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (lieOrderCofactor .PSp 2 q) =
      2 * padicValNat 2 (q - 1) + 2 * padicValNat 2 (q + 1) + 1 := by
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have hc : lieOrderCofactor .PSp 2 q = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    simp only [lieOrderCofactor]
    rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by decide)]
  rw [hc, padicValNat.mul h2 h4, padicValNat_pow_four_sub_one hq hq1,
    padicValNat_sq_sub_one hq hq1]
  omega

theorem padicValNat_lieOrderCofactor_g2 (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (lieOrderCofactor .G2 n q) =
      2 * padicValNat 2 (q - 1) + 2 * padicValNat 2 (q + 1) := by
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h6 : q ^ 6 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  simp only [lieOrderCofactor]
  rw [padicValNat.mul h6 h2, padicValNat_pow_six_sub_one hq hq1, padicValNat_sq_sub_one hq hq1]
  omega

theorem padicValNat_lieOrderCofactor_trialityD4 (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (lieOrderCofactor .trialityD4 n q) =
      2 * padicValNat 2 (q - 1) + 2 * padicValNat 2 (q + 1) := by
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h6 : q ^ 6 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h8 : q ^ 8 + q ^ 4 + 1 ≠ 0 := Nat.succ_ne_zero _
  simp only [lieOrderCofactor]
  rw [padicValNat.mul (mul_ne_zero h8 h6) h2, padicValNat.mul h8 h6,
    padicValNat_triality_factor hq, padicValNat_pow_six_sub_one hq hq1,
    padicValNat_sq_sub_one hq hq1]
  omega

theorem padicValNat_lieOrderCofactor_twistedG2 (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (lieOrderCofactor .twistedG2 n q) =
      padicValNat 2 (q - 1) + padicValNat 2 (q + 1) := by
  have h3 : q ^ 3 + 1 ≠ 0 := Nat.succ_ne_zero _
  have h1 : q - 1 ≠ 0 := by omega
  simp only [lieOrderCofactor]
  rw [padicValNat.mul h3 h1, padicValNat_pow_three_add_one hq]
  omega

theorem factorization_two_psl_four (hadm : StatedLieAdmissible .PSL 4 p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .PSL 4 (p ^ f) = lieOrderNumerator .PSL 4 (p ^ f)) :
    N.factorization 2 + (if p ^ f % 4 = 1 then 2 else 1) =
      3 * padicValNat 2 (p ^ f - 1) + 2 * padicValNat 2 (p ^ f + 1) + 1 := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_of_order hadm hp2 hN
  rwa [show lieOrderDivisor .PSL 4 (p ^ f) = Nat.gcd 4 (p ^ f - 1) from rfl,
    padicValNat_gcd_four_sub_one hq hq1, padicValNat_lieOrderCofactor_psl_four hq hq1] at h

theorem factorization_two_psu_four (hadm : StatedLieAdmissible .PSU 4 p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .PSU 4 (p ^ f) = lieOrderNumerator .PSU 4 (p ^ f)) :
    N.factorization 2 + (if p ^ f % 4 = 3 then 2 else 1) =
      2 * padicValNat 2 (p ^ f - 1) + 3 * padicValNat 2 (p ^ f + 1) + 1 := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_of_order hadm hp2 hN
  rwa [show lieOrderDivisor .PSU 4 (p ^ f) = Nat.gcd 4 (p ^ f + 1) from rfl,
    padicValNat_gcd_four_add_one hq, padicValNat_lieOrderCofactor_psu_four hq hq1] at h

theorem psl_four_mod_sixteen (hadm : StatedLieAdmissible .PSL 4 p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .PSL 4 (p ^ f) = lieOrderNumerator .PSL 4 (p ^ f))
    (h9 : N.factorization 2 = 9) : p ^ f % 16 = 7 := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_psl_four hadm hp2 hN
  rw [h9] at h
  have hodd := Nat.odd_iff.mp hq
  rcases (show p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 by omega) with h4 | h4
  · obtain ⟨hu, hw⟩ := padicValNat_of_mod_four_eq_one hq1 h4
    rw [if_pos h4, hw] at h
    omega
  · obtain ⟨hu, -⟩ := padicValNat_of_mod_four_eq_three h4
    rw [if_neg (by omega), hu] at h
    have hw3 : padicValNat 2 (p ^ f + 1) = 3 := by omega
    have h0 : p ^ f + 1 ≠ 0 := Nat.succ_ne_zero _
    have h8 : 2 ^ 3 ∣ p ^ f + 1 := (padicValNat_dvd_iff_le h0).mpr hw3.ge
    have h16 : ¬ 2 ^ 4 ∣ p ^ f + 1 := fun hd => by
      have := (padicValNat_dvd_iff_le h0).mp hd
      omega
    norm_num at h8 h16
    omega

theorem psu_four_mod_sixteen (hadm : StatedLieAdmissible .PSU 4 p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .PSU 4 (p ^ f) = lieOrderNumerator .PSU 4 (p ^ f))
    (h9 : N.factorization 2 = 9) : p ^ f % 16 = 9 := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_psu_four hadm hp2 hN
  rw [h9] at h
  have hodd := Nat.odd_iff.mp hq
  rcases (show p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 by omega) with h4 | h4
  · obtain ⟨hu, hw⟩ := padicValNat_of_mod_four_eq_one hq1 h4
    rw [if_neg (by omega), hw] at h
    have hu3 : padicValNat 2 (p ^ f - 1) = 3 := by omega
    have h0 : p ^ f - 1 ≠ 0 := by omega
    have h8 : 2 ^ 3 ∣ p ^ f - 1 := (padicValNat_dvd_iff_le h0).mpr hu3.ge
    have h16 : ¬ 2 ^ 4 ∣ p ^ f - 1 := fun hd => by
      have := (padicValNat_dvd_iff_le h0).mp hd
      omega
    norm_num at h8 h16
    omega
  · obtain ⟨hu, hw⟩ := padicValNat_of_mod_four_eq_three h4
    rw [if_pos h4, hu] at h
    omega

theorem psl_four_of_two_part (hadm : StatedLieAdmissible .PSL 4 p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .PSL 4 (p ^ f) = lieOrderNumerator .PSL 4 (p ^ f))
    (h9 : N.factorization 2 = 9) : p ^ f % 4 = 3 ∧ 16 ∣ (p ^ f) ^ 2 - 1 := by
  have h := psl_four_mod_sixteen hadm hp2 hN h9
  have h2 : (p ^ f) ^ 2 % 16 = 1 := by rw [Nat.pow_mod, h]
  omega

theorem psu_four_of_two_part (hadm : StatedLieAdmissible .PSU 4 p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .PSU 4 (p ^ f) = lieOrderNumerator .PSU 4 (p ^ f))
    (h9 : N.factorization 2 = 9) : p ^ f % 4 = 1 ∧ 16 ∣ (p ^ f) ^ 2 - 1 := by
  have h := psu_four_mod_sixteen hadm hp2 hN h9
  have h2 : (p ^ f) ^ 2 % 16 = 1 := by rw [Nat.pow_mod, h]
  omega

theorem factorization_two_psp_two (hadm : StatedLieAdmissible .PSp 2 p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .PSp 2 (p ^ f) = lieOrderNumerator .PSp 2 (p ^ f)) :
    N.factorization 2 = 2 * (padicValNat 2 (p ^ f - 1) + padicValNat 2 (p ^ f + 1)) := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_of_order hadm hp2 hN
  rw [show lieOrderDivisor .PSp 2 (p ^ f) = Nat.gcd 2 (p ^ f - 1) from rfl,
    padicValNat_gcd_two_sub_one hq, padicValNat_lieOrderCofactor_psp_two hq hq1] at h
  omega

theorem factorization_two_g2 (hadm : StatedLieAdmissible .G2 n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .G2 n (p ^ f) = lieOrderNumerator .G2 n (p ^ f)) :
    N.factorization 2 = 2 * (padicValNat 2 (p ^ f - 1) + padicValNat 2 (p ^ f + 1)) := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_of_order hadm hp2 hN
  rw [show lieOrderDivisor .G2 n (p ^ f) = 1 from rfl, padicValNat.one,
    padicValNat_lieOrderCofactor_g2 hq hq1] at h
  omega

theorem factorization_two_trialityD4 (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .trialityD4 n (p ^ f) = lieOrderNumerator .trialityD4 n (p ^ f)) :
    N.factorization 2 = 2 * (padicValNat 2 (p ^ f - 1) + padicValNat 2 (p ^ f + 1)) := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_of_order hadm hp2 hN
  rw [show lieOrderDivisor .trialityD4 n (p ^ f) = 1 from rfl, padicValNat.one,
    padicValNat_lieOrderCofactor_trialityD4 hq hq1] at h
  omega

theorem psp_two_two_part_ne (hadm : StatedLieAdmissible .PSp 2 p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .PSp 2 (p ^ f) = lieOrderNumerator .PSp 2 (p ^ f)) :
    N.factorization 2 ≠ 9 := by
  have := factorization_two_psp_two hadm hp2 hN
  omega

theorem g2_two_part_ne (hadm : StatedLieAdmissible .G2 n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .G2 n (p ^ f) = lieOrderNumerator .G2 n (p ^ f)) :
    N.factorization 2 ≠ 9 := by
  have := factorization_two_g2 hadm hp2 hN
  omega

theorem trialityD4_two_part_ne (hadm : StatedLieAdmissible .trialityD4 n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .trialityD4 n (p ^ f) = lieOrderNumerator .trialityD4 n (p ^ f)) :
    N.factorization 2 ≠ 9 := by
  have := factorization_two_trialityD4 hadm hp2 hN
  omega

theorem factorization_two_twistedG2 (hadm : StatedLieAdmissible .twistedG2 n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .twistedG2 n (p ^ f) = lieOrderNumerator .twistedG2 n (p ^ f)) :
    N.factorization 2 = 3 := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_of_order hadm hp2 hN
  rw [show lieOrderDivisor .twistedG2 n (p ^ f) = 1 from rfl, padicValNat.one,
    padicValNat_lieOrderCofactor_twistedG2 hq hq1] at h
  obtain ⟨-, -, -, rfl, hf, -⟩ := hadm
  rw [padicValNat_three_pow_sub_one_of_odd hf, padicValNat_three_pow_add_one_of_odd hf] at h
  omega

theorem twistedG2_two_part_ne (hadm : StatedLieAdmissible .twistedG2 n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor .twistedG2 n (p ^ f) = lieOrderNumerator .twistedG2 n (p ^ f)) :
    N.factorization 2 ≠ 9 := by
  have := factorization_two_twistedG2 hadm hp2 hN
  omega

theorem two_pow_twelve_dvd_lieOrderCofactor (hq : Odd q) (hq1 : 1 < q)
    (ht : t ∈ ({.F4, .E6, .E7, .E8, .twistedE6} : Finset StatedLieTag)) :
    2 ^ 12 ∣ lieOrderCofactor t n q := by
  have h := two_pow_twelve_dvd hq hq1
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact h.trans ⟨q ^ 6 - 1, by simp only [lieOrderCofactor]; ring⟩
  · exact h.trans ⟨(q ^ 9 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1), by simp only [lieOrderCofactor]; ring⟩
  · exact h.trans ⟨(q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 10 - 1) * (q ^ 6 - 1),
      by simp only [lieOrderCofactor]; ring⟩
  · exact h.trans ⟨(q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1),
      by simp only [lieOrderCofactor]; ring⟩
  · exact h.trans ⟨(q ^ 9 + 1) * (q ^ 6 - 1) * (q ^ 5 + 1), by simp only [lieOrderCofactor]; ring⟩

theorem padicValNat_lieOrderDivisor_le_one (hq : Odd q)
    (ht : t ∈ ({.F4, .E6, .E7, .E8, .twistedE6} : Finset StatedLieTag)) :
    padicValNat 2 (lieOrderDivisor t n q) ≤ 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · show padicValNat 2 1 ≤ 1
    simp
  · show padicValNat 2 (Nat.gcd 3 (q - 1)) ≤ 1
    rw [padicValNat_gcd_three]
    norm_num
  · show padicValNat 2 (Nat.gcd 2 (q - 1)) ≤ 1
    rw [padicValNat_gcd_two_sub_one hq]
  · show padicValNat 2 1 ≤ 1
    simp
  · show padicValNat 2 (Nat.gcd 3 (q + 1)) ≤ 1
    rw [padicValNat_gcd_three]
    norm_num

theorem exceptional_two_part_ge
    (ht : t ∈ ({.F4, .E6, .E7, .E8, .twistedE6} : Finset StatedLieTag))
    (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f)) :
    11 ≤ N.factorization 2 := by
  have hq := odd_pow_of_admissible hadm hp2
  have hq1 := one_lt_pow_of_admissible hadm
  have h := factorization_two_of_order hadm hp2 hN
  have h12 : 12 ≤ padicValNat 2 (lieOrderCofactor t n (p ^ f)) :=
    (padicValNat_dvd_iff_le (p := 2) (n := 12) (lieOrderCofactor_ne_zero hadm)).mp
      (two_pow_twelve_dvd_lieOrderCofactor hq hq1 ht)
  have hd := padicValNat_lieOrderDivisor_le_one (n := n) hq ht
  omega

theorem exceptional_two_part_ne
    (ht : t ∈ ({.F4, .E6, .E7, .E8, .twistedE6} : Finset StatedLieTag))
    (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f)) :
    N.factorization 2 ≠ 9 := by
  have := exceptional_two_part_ge ht hadm hp2 hN
  omega

end CFSG.ComponentClassification.CatLeafProof
