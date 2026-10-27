module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiDegreeArithmetic
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open scoped BigOperators

variable (m : ℕ)

local notation "q" => 2 ^ (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m
local notation "Der" => {g : SzG // suzukiDerangement m g}
local notation "Classes" => suzukiDerangementCentralizerClasses m

theorem suzuki_field_card_ge_two : 2 ≤ q := by
  have h := Nat.pow_le_pow_right (n := 2) (by norm_num) (i := 1) (j := 2 * m + 1) (by omega)
  simpa only [pow_one] using h

theorem suzuki_derangement_card_pos
    (hm : 0 < m) : 0 < Nat.card Der := by
  have hq := suzuki_field_card_ge_two m
  have hcount := suzuki_derangement_count m hm
  have hqp : 0 < q := by omega
  have hqm : 0 < q - 1 := by omega
  have hpos : 0 < q ^ 3 * (q - 1) ^ 2 := by positivity
  omega

theorem suzuki_derangement_less_than_half (hm : 0 < m) :
    2 * Nat.card Der < Nat.card SzG := by
  have hq := suzuki_field_card_ge_two m
  have hqd : (q - 1) + 1 = q := Nat.sub_add_cancel (by omega)
  have hlt : q * (q - 1) < q ^ 2 + 1 := by
    have hle : q - 1 ≤ q := Nat.sub_le _ _
    have hmul := Nat.mul_le_mul_left q hle
    nlinarith
  have hcount := suzuki_derangement_count_mul_degree m hm
  have hGpos : 0 < Nat.card SzG := Nat.card_pos
  apply Nat.lt_of_mul_lt_mul_left (a := q ^ 2 + 1)
  calc
    (q ^ 2 + 1) * (2 * Nat.card Der) = q * (q - 1) * Nat.card SzG := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hcount
    _ < (q ^ 2 + 1) * Nat.card SzG := Nat.mul_lt_mul_of_pos_right hlt hGpos

theorem suzuki_derangement_family_contribution_lower_bound (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) :
    Nat.card SzG ≤ 5 * ((Subgroup.normalizer (A.val : Set SzG)).index * (Nat.card A.val - 1)) := by
  have hmin := suzuki_derangement_family_card_ge_five m hm A
  have hk : A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) ≤ 4 :=
    Nat.le_of_dvd (by norm_num) (suzuki_derangement_family_normalizer_index_dvd_four m hm A)
  have hsk : Nat.card A.val * A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) ≤
      5 * (Nat.card A.val - 1) := by
    calc
      _ ≤ Nat.card A.val * 4 := Nat.mul_le_mul_left _ hk
      _ ≤ _ := by omega
  have h := Nat.mul_le_mul_right (Subgroup.normalizer (A.val : Set SzG)).index hsk
  rw [suzuki_derangement_family_normalizer_card_product m A] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

theorem suzuki_derangement_family_card_mul_group_le (hm : 0 < m) :
    Nat.card Classes * Nat.card SzG ≤ 5 * Nat.card Der := by
  classical
  let := Fintype.ofFinite Classes
  calc
    Nat.card Classes * Nat.card SzG = ∑ _c : Classes, Nat.card SzG := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ ≤ ∑ c : Classes, 5 *
        ((Subgroup.normalizer ((suzukiDerangementCentralizerRepresentative m c).val : Set SzG)).index *
          (Nat.card (suzukiDerangementCentralizerRepresentative m c).val - 1)) := by
      apply Finset.sum_le_sum
      intro c _hc
      exact suzuki_derangement_family_contribution_lower_bound m hm _
    _ = 5 * Nat.card Der := by
      rw [← Finset.mul_sum, ← suzuki_derangement_family_partition_count m hm]

theorem suzuki_derangement_family_card_le_two
    (hm : 0 < m) : Nat.card Classes ≤ 2 := by
  have hsum := suzuki_derangement_family_card_mul_group_le m hm
  have hhalf := suzuki_derangement_less_than_half m hm
  have hGpos : 0 < Nat.card SzG := Nat.card_pos
  by_contra h
  have hr : 3 ≤ Nat.card Classes := by omega
  have hmul := Nat.mul_le_mul_right (Nat.card SzG) hr
  omega

theorem suzuki_derangement_family_nonempty
    (hm : 0 < m) : Nonempty Classes := by
  obtain ⟨g⟩ := (Nat.card_pos_iff.mp (suzuki_derangement_card_pos m hm)).1
  let A : suzukiDerangementCentralizers m :=
    ⟨Subgroup.centralizer ({g.val} : Set SzG), g.val, g.property, rfl⟩
  exact ⟨Quotient.mk'' A⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
