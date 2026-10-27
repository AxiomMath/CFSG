module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiHall
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups

theorem even_square_add_one_coprime_succ (q : ℕ) (hq : Even q) :
    Nat.Coprime (q ^ 2 + 1) (q + 1) := by
  apply Nat.coprime_of_dvd
  intro p hp hpN hpQ
  have hpSq : p ∣ (q + 1) ^ 2 := by
    simpa only [pow_two] using dvd_mul_of_dvd_left hpQ (q + 1)
  have hsq : (q + 1) ^ 2 = (q ^ 2 + 1) + 2 * q := by ring
  have hp2q : p ∣ 2 * q := (Nat.dvd_add_iff_right hpN).mpr (hsq ▸ hpSq)
  rcases hp.dvd_mul.mp hp2q with hp2 | hpq
  · have hpEq : p = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h1 | h2
      · exact False.elim (hp.ne_one h1)
      · exact h2
    exact hq.add_one.not_two_dvd_nat (hpEq ▸ hpQ)
  · have hp1 : p ∣ 1 := (Nat.dvd_add_iff_right hpq).mpr hpQ
    exact hp.not_dvd_one hp1

variable (m : ℕ)

local notation "q" => 2 ^ (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m

theorem suzuki_degree_odd : Odd (q ^ 2 + 1) :=
  ((even_two.pow_of_ne_zero (by omega : 2 * m + 1 ≠ 0)).pow_of_ne_zero
    (by norm_num : 2 ≠ 0)).add_one

theorem suzuki_degree_not_three_dvd : ¬ 3 ∣ q ^ 2 + 1 := by
  have hsq : q ^ 2 = 4 ^ (2 * m + 1) := by
    rw [← pow_mul, show (2 * m + 1) * 2 = 2 * (2 * m + 1) by omega, pow_mul]
    norm_num
  rw [hsq, Nat.dvd_iff_mod_eq_zero]
  norm_num [Nat.add_mod, Nat.pow_mod]

theorem suzuki_degree_coprime_field_succ : Nat.Coprime (q ^ 2 + 1) (q + 1) :=
  even_square_add_one_coprime_succ q (even_two.pow_of_ne_zero (by omega))

theorem suzuki_derangement_family_card_ge_five (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) : 5 ≤ Nat.card A.val := by
  have hgt := suzuki_derangement_family_card_gt_one m A
  obtain ⟨k, hk⟩ := (suzuki_derangement_family_cyclic_odd m hm A).2
  have hne3 : Nat.card A.val ≠ 3 := by
    intro h
    exact suzuki_degree_not_three_dvd m (h ▸ suzuki_derangement_family_card_dvd m hm A)
  omega

theorem suzuki_derangement_family_normalizer_index_pos
    (A : suzukiDerangementCentralizers m) :
    0 < A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hindex := Subgroup.relIndex_mul_index
    (H := A.val) (K := Subgroup.normalizer (A.val : Set SzG)) Subgroup.le_normalizer
  have hcard := Subgroup.card_mul_index A.val
  rw [hzero, zero_mul] at hindex
  rw [← hindex, mul_zero] at hcard
  exact (Nat.card_pos (α := SzG)).ne' hcard.symm

theorem suzuki_derangement_family_normalizer_ambient_index_pos
    (A : suzukiDerangementCentralizers m) :
    0 < (Subgroup.normalizer (A.val : Set SzG)).index :=
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

theorem suzuki_derangement_family_normalizer_card_product
    (A : suzukiDerangementCentralizers m) :
    Nat.card A.val * A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) *
      (Subgroup.normalizer (A.val : Set SzG)).index = Nat.card SzG := by
  calc
    Nat.card A.val * A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) *
        (Subgroup.normalizer (A.val : Set SzG)).index =
        Nat.card A.val * (A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) *
          (Subgroup.normalizer (A.val : Set SzG)).index) := by ring
    _ = Nat.card A.val * A.val.index := by rw [Subgroup.relIndex_mul_index Subgroup.le_normalizer]
    _ = Nat.card SzG := Subgroup.card_mul_index A.val

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
