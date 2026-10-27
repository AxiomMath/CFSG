module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiFamilyBounds
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups
open scoped BigOperators

theorem single_derangement_family_arithmetic_impossible
    (q s k : ℕ) (hq : 4 ≤ q) (hs : 5 ≤ s) (hk : k ∣ 4)
    (hcop : Nat.Coprime (q ^ 2 + 1) (q + 1))
    (hcount : 2 * (q ^ 2 + 1) * (s - 1) = q * (q - 1) * (s * k)) : False := by
  have hqsub : (q - 1) + 1 = q := Nat.sub_add_cancel (by omega)
  have hssub : (s - 1) + 1 = s := Nat.sub_add_cancel (by omega)
  have hspos : 0 < s := by omega
  have hcases : k = 1 ∨ k = 2 ∨ k = 4 := by
    have hle : k ≤ 4 := Nat.le_of_dvd (by norm_num) hk
    have hk0 : k ≠ 0 := by intro h; rw [h] at hk; norm_num at hk
    have hk3 : k ≠ 3 := by intro h; rw [h] at hk; norm_num at hk
    omega
  let d := q - 1
  let e := s - 1
  have hqd : q = d + 1 := hqsub.symm
  have hse : s = e + 1 := hssub.symm
  rcases hcases with rfl | rfl | rfl
  · have hlt : q * (q - 1) < q ^ 2 + 1 := by
      rw [hqd, Nat.add_sub_cancel]
      nlinarith
    have hscaled := Nat.mul_lt_mul_of_pos_right hlt hspos
    have hhalf : s ≤ 2 * (s - 1) := by omega
    have hlower := Nat.mul_le_mul_left (q ^ 2 + 1) hhalf
    have hstrict : q * (q - 1) * (s * 1) < 2 * (q ^ 2 + 1) * (s - 1) := by
      simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using lt_of_lt_of_le hscaled hlower
    exact (ne_of_lt hstrict) hcount.symm
  · have heq : (q + 1) * s = q ^ 2 + 1 := by
      rw [hqd, hse, Nat.add_sub_cancel] at hcount
      simp only [Nat.add_sub_cancel] at hcount
      rw [hqd, hse]
      nlinarith only [hcount]
    have hdiv : q + 1 ∣ q ^ 2 + 1 := ⟨s, heq.symm⟩
    have h := Nat.eq_one_of_dvd_coprimes hcop hdiv (dvd_refl (q + 1))
    omega
  · have hN : 2 * (q ^ 2 + 1) < 4 * q * (q - 1) := by
      have hd : 3 ≤ d := by dsimp [d]; omega
      have hdsq := Nat.mul_le_mul hd hd
      rw [hqd, Nat.add_sub_cancel]
      nlinarith
    have hscaled := Nat.mul_lt_mul_of_pos_right hN hspos
    have hleft : 2 * (q ^ 2 + 1) * (s - 1) < 2 * (q ^ 2 + 1) * s :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    have hstrict : 2 * (q ^ 2 + 1) * (s - 1) < q * (q - 1) * (s * 4) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using lt_trans hleft hscaled
    exact (ne_of_lt hstrict) hcount

variable (m : ℕ)

local notation "q" => 2 ^ (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m
local notation "Der" => {g : SzG // suzukiDerangement m g}
local notation "Classes" => suzukiDerangementCentralizerClasses m

theorem suzuki_positive_field_card_ge_eight (hm : 0 < m) : 8 ≤ q := by
  have h := Nat.pow_le_pow_right (n := 2) (by norm_num) (i := 3) (j := 2 * m + 1) (by omega)
  norm_num at h ⊢
  exact h

theorem suzuki_derangement_family_card_ne_one
    (hm : 0 < m) : Nat.card Classes ≠ 1 := by
  classical
  intro hone
  let := Fintype.ofFinite Classes
  obtain ⟨c, hc⟩ := Nat.card_eq_one_iff_exists.mp hone
  let A := suzukiDerangementCentralizerRepresentative m c
  let n := (Subgroup.normalizer (A.val : Set SzG)).index
  let s := Nat.card A.val
  let k := A.val.relIndex (Subgroup.normalizer (A.val : Set SzG))
  have hsingle : Nat.card Der = n * (s - 1) := by
    have hsum := suzuki_derangement_family_partition_count m hm
    rw [hsum]
    apply Finset.sum_eq_single c
    · intro d _hd hdc
      exact False.elim (hdc (hc d))
    · simp
  have hgroup : s * k * n = Nat.card SzG :=
    suzuki_derangement_family_normalizer_card_product m A
  have hcount := suzuki_derangement_count_mul_degree m hm
  rw [hsingle, ← hgroup] at hcount
  have hcancel : 2 * (q ^ 2 + 1) * (s - 1) = q * (q - 1) * (s * k) := by
    apply Nat.eq_of_mul_eq_mul_right (suzuki_derangement_family_normalizer_ambient_index_pos m A)
    change (2 * (q ^ 2 + 1) * (s - 1)) * n = (q * (q - 1) * (s * k)) * n
    calc
      (2 * (q ^ 2 + 1) * (s - 1)) * n = 2 * (q ^ 2 + 1) * (n * (s - 1)) := by ring
      _ = q * (q - 1) * (s * k * n) := hcount
      _ = (q * (q - 1) * (s * k)) * n := by ring
  exact single_derangement_family_arithmetic_impossible q s k
    (by have h := suzuki_positive_field_card_ge_eight m hm; omega)
    (suzuki_derangement_family_card_ge_five m hm A)
    (suzuki_derangement_family_normalizer_index_dvd_four m hm A)
    (suzuki_degree_coprime_field_succ m) hcancel

theorem suzuki_derangement_family_card_eq_two
    (hm : 0 < m) : Nat.card Classes = 2 := by
  have hle := suzuki_derangement_family_card_le_two m hm
  have hne := suzuki_derangement_family_card_ne_one m hm
  let := suzuki_derangement_family_nonempty m hm
  have hpos : 0 < Nat.card Classes := Nat.card_pos
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
