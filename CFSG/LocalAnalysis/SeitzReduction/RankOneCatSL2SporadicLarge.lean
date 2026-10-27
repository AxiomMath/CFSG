module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicBasic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicSix
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.Monster.Schur.Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Co1


theorem catSL2Hyp_false_Co1 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .Co1) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  have h1 := UnitaryPilot.co1_fixed_card_quotient hJ hna e hτ hD
  rw [card_of_lieModel_PSL_two_two hDm] at h1
  exact ordA_one_ne_of_check (B := 28) hn (by norm_num) (by decide) h1

end Co1

section Co2


theorem catSL2Hyp_false_Co2 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .Co2) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, -, -⟩ := h
  exact UnitaryPilot.co2_false_of_fixed_component hJ hna e hτ hD

end Co2

section Co3


theorem catSL2Hyp_false_Co3 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .Co3) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  rcases UnitaryPilot.co3_fixed_card_quotient hJ hna e hτ hD with h1 | h1 <;>
    rw [card_of_lieModel_PSL_two_two hDm] at h1 <;>
    exact ordA_one_ne_of_check (B := 21) hn (by norm_num) (by decide) h1

end Co3

section Fi22


theorem catSL2Hyp_false_Fi22 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .Fi22) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  obtain ⟨hin, hout⟩ := UnitaryPilot.fi22_fixed_card_quotient hJ hna e hτ hD
  by_cases hτin : τ ∈ (MulAut.conj : J →* MulAut J).range
  · have h1 := (hin hτin).1
    rw [card_of_lieModel_PSL_two_two hDm] at h1
    exact ordA_one_ne_of_check (B := 34) hn (by norm_num) (by decide) h1
  · rcases hout hτin with h1 | h1 <;>
      rw [card_of_lieModel_PSL_two_two hDm] at h1 <;>
      exact ordA_one_ne_of_check (B := 34) hn (by norm_num) (by decide) h1

end Fi22

section Fi23


theorem catSL2Hyp_false_Fi23 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .Fi23) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  have h11 := OmegaPilot.fi23_eleven_dvd_card_quotient_center hJ hna e hτ hD
  have hdvd := OmegaPilot.card_quotient_center_dvd_card_of_fixed D
  rw [card_of_lieModel_PSL_two_two hDm] at h11 hdvd
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Fi23) =
    4089470473293004800 from Sporadic.Fi23.card_Fi23] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := two_pow_le_ordA_one (n := n) (by omega)
  have hn62 : n < 62 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (show 2 ^ n < 2 ^ 62 by omega)
  have hcheck : ∀ m ∈ Finset.range 62, 2 ≤ m → 11 ∣ Open.ordA 1 (2 ^ m) →
      ¬ Open.ordA 1 (2 ^ m) ∣ 4089470473293004800 := by decide
  exact hcheck n (Finset.mem_range.mpr hn62) hn h11 hdvd

end Fi23

section Fi24


theorem catSL2Hyp_false_Fi24 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .Fi24Prime)
    {τ : MulAut J} {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  rcases OmegaPilot.fi24_card_quotient_center hJ hna e hτ hD with h1 | h1 | h1 <;>
    rw [card_of_lieModel_PSL_two_two hDm] at h1 <;>
    exact ordA_one_ne_of_check (B := 62) hn (by norm_num) (by decide) h1

end Fi24

section J4


theorem catSL2Hyp_false_J4 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .J4) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, -, -⟩ := h
  exact OmegaPilot.false_of_j4_component hJ hna e hτ hD

end J4

section Th


theorem catSL2Hyp_false_Th {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .Th) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, -, -⟩ := h
  exact LinearPilot.false_of_th_component hJ hna e hτ hD

end Th

section Baby


theorem catSL2Hyp_false_B {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .B) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  rcases OmegaPilot.baby_card_quotient_center hJ hna e hτ hD with h1 | h1 <;>
    rw [card_of_lieModel_PSL_two_two hDm] at h1 <;>
    exact ordA_one_ne_of_check (B := 77) hn (by norm_num) (by decide) h1

end Baby

section Monster


theorem catSL2Hyp_false_M {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .M) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  obtain ⟨h41, h42⟩ := OmegaPilot.monster_two_part_card_quotient_center
    ComponentClassification.CatLeafProof.monsterInnerInput
    ComponentClassification.CatLeafProof.monsterLocalComponentsInput hJ hna e hτ hD
  have hdvd := OmegaPilot.card_quotient_center_dvd_card_of_fixed D
  rw [card_of_lieModel_PSL_two_two hDm] at h41 h42 hdvd
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    have hev : Even ((2 ^ n) ^ 2) := by
      rw [← pow_mul]
      exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hpos : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact Nat.Even.sub_odd hpos hev odd_one
  obtain rfl : n = 41 := OmegaPilot.eq_forty_one_of_two_part hodd
    (RankThree.PartOne.S12K.ordA_one_eq (by omega)) h41 h42
  have : IsSimpleGroup J := hJ
  obtain ⟨eM⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  rw [Nat.card_congr eM.toEquiv, Monster.Schur.natCard_Gmat_eq] at hdvd
  revert hdvd
  decide

end Monster

end CFSG.SeitzReduction.RankOne
