module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiFamilyNormalizer
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups

theorem two_full_family_count_order_relation
    (q s r n l groupCard derCard : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (hGpos : 0 < groupCard)
    (hA : groupCard = s * 4 * n) (hB : groupCard = r * 4 * l)
    (hDer : derCard = n * (s - 1) + l * (r - 1))
    (hcount : 2 * (q ^ 2 + 1) * derCard = q * (q - 1) * groupCard) :
    (q ^ 2 + 1) * (s + r) = 2 * (q + 1) * (s * r) := by
  have hAr : groupCard * r = (s * 4 * n) * r :=
    congrArg (fun x : ℕ => x * r) hA
  have hBs : groupCard * s = (r * 4 * l) * s :=
    congrArg (fun x : ℕ => x * s) hB
  have hrel : 2 * (q ^ 2 + 1) * (r * (s - 1) + s * (r - 1)) =
      4 * q * (q - 1) * (s * r) := by
    apply Nat.eq_of_mul_eq_mul_right hGpos
    calc
      (2 * (q ^ 2 + 1) * (r * (s - 1) + s * (r - 1))) * groupCard =
          2 * (q ^ 2 + 1) *
            ((groupCard * r) * (s - 1) + (groupCard * s) * (r - 1)) := by ring
      _ = 2 * (q ^ 2 + 1) *
          (((s * 4 * n) * r) * (s - 1) + ((r * 4 * l) * s) * (r - 1)) := by
        rw [hAr, hBs]
      _ = (4 * s * r) * (2 * (q ^ 2 + 1) * derCard) := by rw [hDer]; ring
      _ = (4 * s * r) * (q * (q - 1) * groupCard) := by rw [hcount]
      _ = (4 * q * (q - 1) * (s * r)) * groupCard := by ring
  let d := q - 1
  let e := s - 1
  let f := r - 1
  have hqd : q = d + 1 := (Nat.sub_add_cancel hq).symm
  have hse : s = e + 1 := (Nat.sub_add_cancel hs).symm
  have hrf : r = f + 1 := (Nat.sub_add_cancel hr).symm
  rw [hqd, hse, hrf] at hrel ⊢
  simp only [Nat.add_sub_cancel] at hrel
  nlinarith only [hrel]

theorem coprime_full_degree_count_orders (q s r : ℕ) (hs : 0 < s) (hr : 0 < r)
    (hNodd : Odd (q ^ 2 + 1)) (hNcop : Nat.Coprime (q ^ 2 + 1) (q + 1))
    (hsN : s ∣ q ^ 2 + 1) (hrN : r ∣ q ^ 2 + 1) (hsr : Nat.Coprime s r)
    (hrel : (q ^ 2 + 1) * (s + r) = 2 * (q + 1) * (s * r)) :
    s * r = q ^ 2 + 1 ∧ s + r = 2 * (q + 1) := by
  obtain ⟨d, hd⟩ := hsr.mul_dvd_of_dvd_of_dvd hsN hrN
  have hsrpos : 0 < s * r := Nat.mul_pos hs hr
  have hdsum : d * (s + r) = 2 * (q + 1) := by
    apply Nat.eq_of_mul_eq_mul_left hsrpos
    calc
      (s * r) * (d * (s + r)) = (q ^ 2 + 1) * (s + r) := by rw [hd]; ring
      _ = 2 * (q + 1) * (s * r) := hrel
      _ = (s * r) * (2 * (q + 1)) := by ring
  have hdN : d ∣ q ^ 2 + 1 := ⟨s * r, by rw [hd]; ring⟩
  have hdodd := hNodd.of_dvd_nat hdN
  have hdTwo : Nat.Coprime d 2 := Nat.coprime_two_right.mpr hdodd
  have hd2Q : d ∣ 2 * (q + 1) := ⟨s + r, hdsum.symm⟩
  have hdQ : d ∣ q + 1 := hdTwo.dvd_of_dvd_mul_left hd2Q
  have hd1 : d = 1 := Nat.eq_one_of_dvd_coprimes hNcop hdN hdQ
  constructor
  · simpa only [hd1, mul_one] using hd.symm
  · simpa only [hd1, one_mul] using hdsum

variable (m : ℕ)

local notation "q" => 2 ^ (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m
local notation "Der" => {g : SzG // suzukiDerangement m g}
local notation "Classes" => suzukiDerangementCentralizerClasses m

theorem suzuki_derangement_two_family_order_sum_product (hm : 0 < m)
    (c d : Classes) (hcd : c ≠ d) :
    Nat.card (suzukiDerangementCentralizerRepresentative m c).val *
        Nat.card (suzukiDerangementCentralizerRepresentative m d).val = q ^ 2 + 1 ∧
      Nat.card (suzukiDerangementCentralizerRepresentative m c).val +
        Nat.card (suzukiDerangementCentralizerRepresentative m d).val = 2 * (q + 1) := by
  let A := suzukiDerangementCentralizerRepresentative m c
  let B := suzukiDerangementCentralizerRepresentative m d
  let s := Nat.card A.val
  let r := Nat.card B.val
  let n := (Subgroup.normalizer (A.val : Set SzG)).index
  let l := (Subgroup.normalizer (B.val : Set SzG)).index
  have hs : 0 < s := by have h := suzuki_derangement_family_card_ge_five m hm A; omega
  have hr : 0 < r := by have h := suzuki_derangement_family_card_ge_five m hm B; omega
  have hA : Nat.card SzG = s * 4 * n := by
    have h := suzuki_derangement_family_normalizer_card_product m A
    rw [suzuki_derangement_family_normalizer_index_eq_four m hm c] at h
    exact h.symm
  have hB : Nat.card SzG = r * 4 * l := by
    have h := suzuki_derangement_family_normalizer_card_product m B
    rw [suzuki_derangement_family_normalizer_index_eq_four m hm d] at h
    exact h.symm
  have hDer : Nat.card Der = n * (s - 1) + l * (r - 1) :=
    suzuki_derangement_two_family_count m hm c d hcd
  have hrel := two_full_family_count_order_relation q s r n l (Nat.card SzG) (Nat.card Der)
    (by have h := suzuki_field_card_ge_two m; omega) (by omega) (by omega)
    Nat.card_pos hA hB hDer (suzuki_derangement_count_mul_degree m hm)
  exact coprime_full_degree_count_orders q s r hs hr (suzuki_degree_odd m)
    (suzuki_degree_coprime_field_succ m) (suzuki_derangement_family_card_dvd m hm A)
    (suzuki_derangement_family_card_dvd m hm B)
    (suzuki_derangement_distinct_family_coprime m hm c d hcd) hrel

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
