module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiTwoFamilies
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups
open scoped BigOperators

variable (m : ℕ)

local notation "SzG" => SuzukiMatrixGroup m
local notation "Der" => {g : SzG // suzukiDerangement m g}
local notation "Classes" => suzukiDerangementCentralizerClasses m

theorem suzuki_derangement_two_family_count
    (hm : 0 < m) (c d : Classes) (hcd : c ≠ d) :
    Nat.card Der =
      (Subgroup.normalizer ((suzukiDerangementCentralizerRepresentative m c).val : Set SzG)).index *
        (Nat.card (suzukiDerangementCentralizerRepresentative m c).val - 1) +
      (Subgroup.normalizer ((suzukiDerangementCentralizerRepresentative m d).val : Set SzG)).index *
        (Nat.card (suzukiDerangementCentralizerRepresentative m d).val - 1) := by
  classical
  let := Fintype.ofFinite Classes
  obtain ⟨e, _he, huniq⟩ := (Nat.card_eq_two_iff' c).mp (suzuki_derangement_family_card_eq_two m hm)
  have hde : d = e := huniq d hcd.symm
  have hcover (x : Classes) : x = c ∨ x = d := by
    by_cases hx : x = c
    · exact Or.inl hx
    · exact Or.inr ((huniq x hx).trans hde.symm)
  have huniv : (Finset.univ : Finset Classes) = {c, d} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcover x
  rw [suzuki_derangement_family_partition_count m hm, huniv, Finset.sum_pair hcd]

theorem suzuki_derangement_family_small_normalizer_contribution
    (hm : 0 < m)
    (A : suzukiDerangementCentralizers m)
    (hk : A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) ≤ 2) :
    2 * Nat.card SzG ≤ 5 * ((Subgroup.normalizer (A.val : Set SzG)).index * (Nat.card A.val - 1)) := by
  have hs := suzuki_derangement_family_card_ge_five m hm A
  have hsk : 2 * (Nat.card A.val * A.val.relIndex (Subgroup.normalizer (A.val : Set SzG))) ≤
      5 * (Nat.card A.val - 1) := by
    have h := Nat.mul_le_mul_left (Nat.card A.val) hk
    omega
  have h := Nat.mul_le_mul_right (Subgroup.normalizer (A.val : Set SzG)).index hsk
  calc
    2 * Nat.card SzG =
        (2 * (Nat.card A.val * A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)))) *
          (Subgroup.normalizer (A.val : Set SzG)).index := by
      rw [← suzuki_derangement_family_normalizer_card_product m A]
      ring
    _ ≤ (5 * (Nat.card A.val - 1)) * (Subgroup.normalizer (A.val : Set SzG)).index := h
    _ = _ := by ring

theorem suzuki_derangement_family_normalizer_index_eq_four
    (hm : 0 < m) (c : Classes) :
    (suzukiDerangementCentralizerRepresentative m c).val.relIndex
      (Subgroup.normalizer ((suzukiDerangementCentralizerRepresentative m c).val : Set SzG)) = 4 := by
  classical
  let A := suzukiDerangementCentralizerRepresentative m c
  by_contra hne
  let k := A.val.relIndex (Subgroup.normalizer (A.val : Set SzG))
  change k ≠ 4 at hne
  have hkdiv := suzuki_derangement_family_normalizer_index_dvd_four m hm A
  have hkle : A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hkdiv
  have hk3 : A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) ≠ 3 := by
    intro h
    rw [h] at hkdiv
    norm_num at hkdiv
  have hk : A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) ≤ 2 := by
    change k ≤ 2
    change k ≤ 4 at hkle
    change k ≠ 3 at hk3
    omega
  obtain ⟨d, hdc, _huniq⟩ := (Nat.card_eq_two_iff' c).mp (suzuki_derangement_family_card_eq_two m hm)
  let B := suzukiDerangementCentralizerRepresentative m d
  have hA := suzuki_derangement_family_small_normalizer_contribution m hm A hk
  have hB := suzuki_derangement_family_contribution_lower_bound m hm B
  have hsum := suzuki_derangement_two_family_count m hm c d hdc.symm
  have hhalf := suzuki_derangement_less_than_half m hm
  have hGpos : 0 < Nat.card SzG := Nat.card_pos
  change Nat.card Der =
    (Subgroup.normalizer (A.val : Set SzG)).index * (Nat.card A.val - 1) +
    (Subgroup.normalizer (B.val : Set SzG)).index * (Nat.card B.val - 1) at hsum
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
