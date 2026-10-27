module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Arith

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

private theorem coprime_two_pow (k : ℕ) {d : ℕ} (hd : d = 1 ∨ d = 5) :
    Nat.Coprime (2 ^ k) d := by
  rcases hd with rfl | rfl
  · exact Nat.coprime_one_right _
  · exact Nat.Coprime.pow_left _ (by decide)

private theorem lt_of_pow_dvd {N V p : ℕ} (hV : 2 ^ V ∣ N) (hnot : ¬ 2 ^ p ∣ N) : V < p := by
  by_contra h
  exact hnot ((Nat.pow_dvd_pow 2 (by omega : p ≤ V)).trans hV)

private theorem not_thm54Order_251596800 : ¬ Thm54Order 251596800 := by
  intro hc
  rcases hc with ⟨f, hf, hodd, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have hV : 2 ^ (2 * f) ∣ 251596800 :=
      ⟨(2 ^ (2 * f) + 1) * (2 ^ f - 1), hce⟩
    have hfub : f ≤ 6 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 251596800)
      omega
    interval_cases f <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (4 * m) ∣ 251596800 :=
      ⟨((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)), hce⟩
    have hmub : m ≤ 3 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 251596800)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (6 * m) ∣ 251596800 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 251596800)
    omega
  · have hV : 2 ^ (6 * m) ∣ 251596800 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 251596800)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 251596800 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 251596800)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 251596800 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 251596800)
    omega

private theorem not_thm54Order_3311126603366400 : ¬ Thm54Order 3311126603366400 := by
  intro hc
  rcases hc with ⟨f, hf, hodd, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have hV : 2 ^ (2 * f) ∣ 3311126603366400 :=
      ⟨(2 ^ (2 * f) + 1) * (2 ^ f - 1), hce⟩
    have hfub : f ≤ 12 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 25 ∣ 3311126603366400)
      omega
    interval_cases f <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (4 * m) ∣ 3311126603366400 :=
      ⟨((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)), hce⟩
    have hmub : m ≤ 6 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 25 ∣ 3311126603366400)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (6 * m) ∣ 3311126603366400 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))), hce⟩
    have hmub : m ≤ 4 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 25 ∣ 3311126603366400)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (6 * m) ∣ 3311126603366400 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))), hce⟩
    have hmub : m ≤ 4 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 25 ∣ 3311126603366400)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 3311126603366400 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 25 ∣ 3311126603366400)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 3311126603366400 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 25 ∣ 3311126603366400)
    omega

private theorem not_thm54Order_76532479683774853939200 : ¬ Thm54Order 76532479683774853939200 := by
  intro hc
  rcases hc with ⟨f, hf, hodd, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have hV : 2 ^ (2 * f) ∣ 76532479683774853939200 :=
      ⟨(2 ^ (2 * f) + 1) * (2 ^ f - 1), hce⟩
    have hfub : f ≤ 18 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 37 ∣ 76532479683774853939200)
      omega
    interval_cases f <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (4 * m) ∣ 76532479683774853939200 :=
      ⟨((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)), hce⟩
    have hmub : m ≤ 9 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 37 ∣ 76532479683774853939200)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (6 * m) ∣ 76532479683774853939200 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))), hce⟩
    have hmub : m ≤ 6 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 37 ∣ 76532479683774853939200)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (6 * m) ∣ 76532479683774853939200 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))), hce⟩
    have hmub : m ≤ 6 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 37 ∣ 76532479683774853939200)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 76532479683774853939200 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have hm3 : m = 3 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 37 ∣ 76532479683774853939200)
      omega
    subst m
    rcases hd with rfl | rfl <;> exact absurd hcd (by norm_num)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 76532479683774853939200 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have hm3 : m = 3 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 37 ∣ 76532479683774853939200)
      omega
    subst m
    rcases hd with rfl | rfl <;> exact absurd hcd (by norm_num)

private theorem not_thm54Order_1451520 : ¬ Thm54Order 1451520 := by
  intro hc
  rcases hc with ⟨f, hf, hodd, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have hV : 2 ^ (2 * f) ∣ 1451520 :=
      ⟨(2 ^ (2 * f) + 1) * (2 ^ f - 1), hce⟩
    have hfub : f ≤ 4 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 10 ∣ 1451520)
      omega
    interval_cases f <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (4 * m) ∣ 1451520 :=
      ⟨((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 10 ∣ 1451520)
    omega
  · have hV : 2 ^ (6 * m) ∣ 1451520 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 10 ∣ 1451520)
    omega
  · have hV : 2 ^ (6 * m) ∣ 1451520 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 10 ∣ 1451520)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 1451520 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 10 ∣ 1451520)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 1451520 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 10 ∣ 1451520)
    omega

private theorem not_thm54Order_9196830720 : ¬ Thm54Order 9196830720 := by
  intro hc
  rcases hc with ⟨f, hf, hodd, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have hV : 2 ^ (2 * f) ∣ 9196830720 :=
      ⟨(2 ^ (2 * f) + 1) * (2 ^ f - 1), hce⟩
    have hfub : f ≤ 7 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 16 ∣ 9196830720)
      omega
    interval_cases f <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (4 * m) ∣ 9196830720 :=
      ⟨((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)), hce⟩
    have hmub : m ≤ 3 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 16 ∣ 9196830720)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (6 * m) ∣ 9196830720 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 16 ∣ 9196830720)
    omega
  · have hV : 2 ^ (6 * m) ∣ 9196830720 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 16 ∣ 9196830720)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 9196830720 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 16 ∣ 9196830720)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 9196830720 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 16 ∣ 9196830720)
    omega

private theorem not_thm54Order_174182400 : ¬ Thm54Order 174182400 := by
  intro hc
  rcases hc with ⟨f, hf, hodd, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have hV : 2 ^ (2 * f) ∣ 174182400 :=
      ⟨(2 ^ (2 * f) + 1) * (2 ^ f - 1), hce⟩
    have hfub : f ≤ 6 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 174182400)
      omega
    interval_cases f <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (4 * m) ∣ 174182400 :=
      ⟨((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)), hce⟩
    have hmub : m ≤ 3 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 174182400)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (6 * m) ∣ 174182400 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 174182400)
    omega
  · have hV : 2 ^ (6 * m) ∣ 174182400 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 174182400)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 174182400 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 174182400)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 174182400 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 174182400)
    omega

private theorem not_thm54Order_197406720 : ¬ Thm54Order 197406720 := by
  intro hc
  rcases hc with ⟨f, hf, hodd, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ | ⟨m, hm, hce⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have hV : 2 ^ (2 * f) ∣ 197406720 :=
      ⟨(2 ^ (2 * f) + 1) * (2 ^ f - 1), hce⟩
    have hfub : f ≤ 6 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 197406720)
      omega
    interval_cases f <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (4 * m) ∣ 197406720 :=
      ⟨((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)), hce⟩
    have hmub : m ≤ 3 := by
      have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 197406720)
      omega
    interval_cases m <;> exact absurd hce (by norm_num)
  · have hV : 2 ^ (6 * m) ∣ 197406720 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 197406720)
    omega
  · have hV : 2 ^ (6 * m) ∣ 197406720 :=
      ⟨((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))), hce⟩
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 197406720)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 197406720 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 197406720)
    omega
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hV : 2 ^ (10 * m) ∣ 197406720 :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have := lt_of_pow_dvd hV (by norm_num : ¬ 2 ^ 13 ∣ 197406720)
    omega

theorem Thm54Order.ne_residual {c : ℕ} (hc : Thm54Order c) :
    c ≠ 251596800 ∧
      c ≠ 3311126603366400 ∧
      c ≠ 76532479683774853939200 ∧
      c ≠ 1451520 ∧
      c ≠ 9196830720 ∧
      c ≠ 174182400 ∧
      c ≠ 197406720 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h] at hc; exact not_thm54Order_251596800 hc
  · rw [h] at hc; exact not_thm54Order_3311126603366400 hc
  · rw [h] at hc; exact not_thm54Order_76532479683774853939200 hc
  · rw [h] at hc; exact not_thm54Order_1451520 hc
  · rw [h] at hc; exact not_thm54Order_9196830720 hc
  · rw [h] at hc; exact not_thm54Order_174182400 hc
  · rw [h] at hc; exact not_thm54Order_197406720 hc

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
