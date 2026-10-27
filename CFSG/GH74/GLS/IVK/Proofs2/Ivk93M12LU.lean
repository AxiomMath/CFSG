module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Crit
public import CFSG.GH74.Generic.Context
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Arith

theorem ivk93m12_two_pow_seven_dvd_sq_mul_fourth (q : ℕ) (hq : Odd q) :
    2 ^ 7 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  have h2 : (2 * k + 1) ^ 4 - 1 = 4 * (k * (k + 1)) * (2 * (2 * k ^ 2 + 2 * k + 1)) := by
    have : (2 * k + 1) ^ 4 = 4 * (k * (k + 1)) * (2 * (2 * k ^ 2 + 2 * k + 1)) + 1 := by ring
    omega
  have hk : 2 ∣ k * (k + 1) := even_iff_two_dvd.1 (Nat.even_mul_succ_self k)
  obtain ⟨t, ht⟩ := hk
  rw [h1, h2, ht]
  exact ⟨t * (t * (2 * k ^ 2 + 2 * k + 1)), by ring⟩

theorem ivk93m12_two_pow_seven_dvd_div_of_dvd_five (N g : ℕ) (hg : g ∣ N) (hg5 : g ∣ 5)
    (h7 : 2 ^ 7 ∣ N) : 2 ^ 7 ∣ N / g := by
  refine Nat.dvd_div_of_mul_dvd ?_
  rw [mul_comm]
  have hc : Nat.Coprime (2 ^ 7) g :=
    Nat.Coprime.pow_left 7 (Nat.Coprime.coprime_dvd_right hg5 (by norm_num))
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h7 hg

theorem ivk93m12_two_pow_seven_dvd_l4 (q : ℕ) (hq : Odd q) :
    2 ^ 7 ∣ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) / Nat.gcd 4 (q - 1) := by
  obtain ⟨k, hk⟩ := hq
  rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
  · have hq : q = 4 * j + 1 := by omega
    subst hq
    have hg : Nat.gcd 4 (4 * j + 1 - 1) = 4 := by
      rw [Nat.add_sub_cancel]
      exact Nat.gcd_eq_left (Dvd.intro j rfl)
    have hA : (4 * j + 1) ^ 2 - 1 = 8 * j * (2 * j + 1) := by
      have : (4 * j + 1) ^ 2 = 8 * j * (2 * j + 1) + 1 := by ring
      omega
    have hB : (4 * j + 1) ^ 3 - 1 = 4 * j * (16 * j ^ 2 + 12 * j + 3) := by
      have : (4 * j + 1) ^ 3 = 4 * j * (16 * j ^ 2 + 12 * j + 3) + 1 := by ring
      omega
    have hC : (4 * j + 1) ^ 4 - 1 = 16 * j * (16 * j ^ 3 + 16 * j ^ 2 + 6 * j + 1) := by
      have : (4 * j + 1) ^ 4 = 16 * j * (16 * j ^ 3 + 16 * j ^ 2 + 6 * j + 1) + 1 := by ring
      omega
    rw [hg, hA, hB, hC]
    refine Nat.dvd_div_of_mul_dvd ?_
    exact ⟨(4 * j + 1) ^ 6 * (j * (2 * j + 1) * (j * (16 * j ^ 2 + 12 * j + 3)) *
      (j * (16 * j ^ 3 + 16 * j ^ 2 + 6 * j + 1))), by ring⟩
  · have hq : q = 4 * j + 3 := by omega
    subst hq
    have hg : Nat.gcd 4 (4 * j + 3 - 1) = 2 := by
      rw [show 4 * j + 3 - 1 = 2 + j * 4 by omega, Nat.gcd_add_mul_right_right]
      decide
    have hA : (4 * j + 3) ^ 2 - 1 = 8 * ((2 * j + 1) * (j + 1)) := by
      have : (4 * j + 3) ^ 2 = 8 * ((2 * j + 1) * (j + 1)) + 1 := by ring
      omega
    have hB : (4 * j + 3) ^ 3 - 1 = 2 * ((2 * j + 1) * (16 * j ^ 2 + 28 * j + 13)) := by
      have : (4 * j + 3) ^ 3 = 2 * ((2 * j + 1) * (16 * j ^ 2 + 28 * j + 13)) + 1 := by ring
      omega
    have hC : (4 * j + 3) ^ 4 - 1 = 16 * ((2 * j + 1) * (j + 1) * (8 * j ^ 2 + 12 * j + 5)) := by
      have : (4 * j + 3) ^ 4 = 16 * ((2 * j + 1) * (j + 1) * (8 * j ^ 2 + 12 * j + 5)) + 1 := by
        ring
      omega
    rw [hg, hA, hB, hC]
    refine Nat.dvd_div_of_mul_dvd ?_
    exact ⟨(4 * j + 3) ^ 6 * (((2 * j + 1) * (j + 1)) *
      ((2 * j + 1) * (16 * j ^ 2 + 28 * j + 13)) *
      ((2 * j + 1) * (j + 1) * (8 * j ^ 2 + 12 * j + 5))), by ring⟩

theorem ivk93m12_two_pow_seven_dvd_u4 (q : ℕ) (hq : Odd q) :
    2 ^ 7 ∣ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / Nat.gcd 4 (q + 1) := by
  obtain ⟨k, hk⟩ := hq
  rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
  · have hq : q = 4 * j + 1 := by omega
    subst hq
    have hg : Nat.gcd 4 (4 * j + 1 + 1) = 2 := by
      rw [show 4 * j + 1 + 1 = 2 + j * 4 by omega, Nat.gcd_add_mul_right_right]
      decide
    have hA : (4 * j + 1) ^ 2 - 1 = 8 * j * (2 * j + 1) := by
      have : (4 * j + 1) ^ 2 = 8 * j * (2 * j + 1) + 1 := by ring
      omega
    have hD : (4 * j + 1) ^ 3 + 1 = 2 * (32 * j ^ 3 + 24 * j ^ 2 + 6 * j + 1) := by ring
    have hC : (4 * j + 1) ^ 4 - 1 = 16 * j * (16 * j ^ 3 + 16 * j ^ 2 + 6 * j + 1) := by
      have : (4 * j + 1) ^ 4 = 16 * j * (16 * j ^ 3 + 16 * j ^ 2 + 6 * j + 1) + 1 := by ring
      omega
    rw [hg, hA, hD, hC]
    refine Nat.dvd_div_of_mul_dvd ?_
    exact ⟨(4 * j + 1) ^ 6 * (j * (2 * j + 1) * (32 * j ^ 3 + 24 * j ^ 2 + 6 * j + 1) *
      (j * (16 * j ^ 3 + 16 * j ^ 2 + 6 * j + 1))), by ring⟩
  · have hq : q = 4 * j + 3 := by omega
    subst hq
    have hg : Nat.gcd 4 (4 * j + 3 + 1) = 4 := by
      rw [show 4 * j + 3 + 1 = 4 * (j + 1) by ring]
      exact Nat.gcd_eq_left (Dvd.intro _ rfl)
    have hA : (4 * j + 3) ^ 2 - 1 = 8 * ((2 * j + 1) * (j + 1)) := by
      have : (4 * j + 3) ^ 2 = 8 * ((2 * j + 1) * (j + 1)) + 1 := by ring
      omega
    have hD : (4 * j + 3) ^ 3 + 1 = 4 * ((j + 1) * (16 * j ^ 2 + 20 * j + 7)) := by ring
    have hC : (4 * j + 3) ^ 4 - 1 = 16 * ((2 * j + 1) * (j + 1) * (8 * j ^ 2 + 12 * j + 5)) := by
      have : (4 * j + 3) ^ 4 = 16 * ((2 * j + 1) * (j + 1) * (8 * j ^ 2 + 12 * j + 5)) + 1 := by
        ring
      omega
    rw [hg, hA, hD, hC]
    refine Nat.dvd_div_of_mul_dvd ?_
    exact ⟨(4 * j + 3) ^ 6 * (((2 * j + 1) * (j + 1)) * ((j + 1) * (16 * j ^ 2 + 20 * j + 7)) *
      ((2 * j + 1) * (j + 1) * (8 * j ^ 2 + 12 * j + 5))), by ring⟩

theorem ivk93m12_two_pow_seven_dvd_l5 (q : ℕ) (hq : Odd q) :
    2 ^ 7 ∣ q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) /
      Nat.gcd 5 (q - 1) := by
  refine ivk93m12_two_pow_seven_dvd_div_of_dvd_five _ _ ?_ (Nat.gcd_dvd_left _ _) ?_
  · have h1 : Nat.gcd 5 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 2 - 1 := by
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2
    exact (h1.trans h2).trans ⟨q ^ 10 * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1))), by ring⟩
  · exact (ivk93m12_two_pow_seven_dvd_sq_mul_fourth q hq).trans
      ⟨q ^ 10 * ((q ^ 3 - 1) * (q ^ 5 - 1)), by ring⟩

theorem ivk93m12_two_pow_seven_dvd_u5 (q : ℕ) (hq : Odd q) :
    2 ^ 7 ∣ q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) /
      Nat.gcd 5 (q + 1) := by
  refine ivk93m12_two_pow_seven_dvd_div_of_dvd_five _ _ ?_ (Nat.gcd_dvd_left _ _) ?_
  · have h1 : Nat.gcd 5 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
    have h2 : q + 1 ∣ q ^ 2 - 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := hq.pos; omega⟩
      have : (k + 1) ^ 2 - 1 = k * (k + 2) := by
        have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
        omega
      rw [this]
      exact ⟨k, by ring⟩
    exact (h1.trans h2).trans ⟨q ^ 10 * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1))), by ring⟩
  · exact (ivk93m12_two_pow_seven_dvd_sq_mul_fourth q hq).trans
      ⟨q ^ 10 * ((q ^ 3 + 1) * (q ^ 5 + 1)), by ring⟩

theorem ivk93m12_toNat_two (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have : (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [this, Int.toNat_natCast]

theorem ivk93m12_toNat_three (q : ℕ) : (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
  have : (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [this, Int.toNat_natCast]

theorem ivk93m12_toNat_four (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℕ) : ℤ) ^ 4 - (-1) ^ 4).toNat = q ^ 4 - 1 := by
  have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have : (((q : ℕ) : ℤ) ^ 4 - (-1) ^ 4) = ((q ^ 4 - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [this, Int.toNat_natCast]

theorem ivk93m12_toNat_five (q : ℕ) : (((q : ℕ) : ℤ) ^ 5 - (-1) ^ 5).toNat = q ^ 5 + 1 := by
  have : (((q : ℕ) : ℤ) ^ 5 - (-1) ^ 5) = ((q ^ 5 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [this, Int.toNat_natCast]

end Arith

section Orders

variable {F : Type} [Field F] [Finite F]

theorem ivk93m12_card_psl4 (hodd : Odd (Nat.card F)) :
    2 ^ 7 ∣ Nat.card (StatedProj (StatedSL 4 F)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num)]
  have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by simp), Finset.prod_pair (by norm_num : (3 : ℕ) ≠ 4)]
  have := ivk93m12_two_pow_seven_dvd_l4 (Nat.card F) hodd
  simpa using this

theorem ivk93m12_card_psl5 (hodd : Odd (Nat.card F)) :
    2 ^ 7 ∣ Nat.card (StatedProj (StatedSL 5 F)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num)]
  have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
  rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_pair (by norm_num : (4 : ℕ) ≠ 5)]
  have := ivk93m12_two_pow_seven_dvd_l5 (Nat.card F) hodd
  simpa using this

theorem ivk93m12_card_psu4 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hodd : Odd (p ^ f)) {K : Type}
    [Field K] (hK : Nat.card K = (p ^ f) ^ 2) : 2 ^ 7 ∣ Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) := by
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by norm_num)]
  have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by simp), Finset.prod_pair (by norm_num : (3 : ℕ) ≠ 4),
    ivk93m12_toNat_two _ hq1, ivk93m12_toNat_three, ivk93m12_toNat_four _ hq1]
  have := ivk93m12_two_pow_seven_dvd_u4 (p ^ f) hodd
  simpa using this

theorem ivk93m12_card_psu5 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hodd : Odd (p ^ f)) {K : Type}
    [Field K] (hK : Nat.card K = (p ^ f) ^ 2) : 2 ^ 7 ∣ Nat.card (StatedProj (StatedSU 5 (p ^ f) K)) := by
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by norm_num)]
  have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
  rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_pair (by norm_num : (4 : ℕ) ≠ 5), ivk93m12_toNat_two _ hq1, ivk93m12_toNat_three,
    ivk93m12_toNat_four _ hq1, ivk93m12_toNat_five]
  have := ivk93m12_two_pow_seven_dvd_u5 (p ^ f) hodd
  simpa using this

end Orders

theorem ivk93m12_l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93M12Empty (fun X _ => LieModel X .PSL 4 p f) := by
  intro p f hp hp2 hf _ J _ _ hJ y D
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  refine D.false_of_two_pow_seven_dvd ?_
  rw [Nat.card_congr e.toEquiv]
  exact ivk93m12_card_psl4 hodd

theorem ivk93m12_l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    Ivk93M12Empty (fun X _ => LieModel X .PSL 5 p f) := by
  intro p f hp hf hmod J _ _ hJ y D
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact Nat.odd_iff.mpr (by omega)
  refine D.false_of_two_pow_seven_dvd ?_
  rw [Nat.card_congr e.toEquiv]
  exact ivk93m12_card_psl5 hodd

theorem ivk93m12_u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93M12Empty (fun X _ => LieModel X .PSU 4 p f) := by
  intro p f hp hp2 hf _ J _ _ hJ y D
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  refine D.false_of_two_pow_seven_dvd ?_
  rw [Nat.card_congr e.toEquiv]
  exact ivk93m12_card_psu4 hp hf hodd hK

theorem ivk93m12_u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
    Ivk93M12Empty (fun X _ => LieModel X .PSU 5 p f) := by
  intro p f hp hf hmod J _ _ hJ y D
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have hodd : Odd (p ^ f) := Nat.odd_iff.mpr (by omega)
  refine D.false_of_two_pow_seven_dvd ?_
  rw [Nat.card_congr e.toEquiv]
  exact ivk93m12_card_psu5 hp hf hodd hK

end CFSG.GH74.GLS.IVK.Proofs2
