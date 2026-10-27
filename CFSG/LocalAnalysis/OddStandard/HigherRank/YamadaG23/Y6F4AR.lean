module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AD
public import CFSG.Blueprint.EvenStandardExact
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum
import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem y6f4a_card_target (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : Y6TargetLie X) :
    Nat.card X = 262080 ∨ Nat.card X = 5515776 ∨ Nat.card X = 16482816 := by
  rcases h with h | h | h
  · obtain ⟨-, h1, -⟩ := hO X .PSL 2 2 6 h.admissible h
    have hd : lieOrderDivisor .PSL 2 (2 ^ 6) = 1 := by decide +kernel
    have hn : lieOrderNumerator .PSL 2 (2 ^ 6) = 262080 := by decide +kernel
    rw [hd, hn] at h1
    exact Or.inl (by simpa using h1)
  · obtain ⟨-, h1, -⟩ := hO X .PSU 3 2 3 h.admissible h
    have hd : lieOrderDivisor .PSU 3 (2 ^ 3) = 3 := by decide +kernel
    have hn : lieOrderNumerator .PSU 3 (2 ^ 3) = 16547328 := by decide +kernel
    rw [hd, hn] at h1
    exact Or.inr (Or.inl (by omega))
  · obtain ⟨-, h1, -⟩ := hO X .PSL 3 2 3 h.admissible h
    have hd : lieOrderDivisor .PSL 3 (2 ^ 3) = 1 := by decide +kernel
    have hn : lieOrderNumerator .PSL 3 (2 ^ 3) = 16482816 := by decide +kernel
    rw [hd, hn] at h1
    exact Or.inr (Or.inr (by simpa using h1))

theorem y6f4a_evenStandardType {X : Type} [Group X] (h : Y6TargetLie X) :
    Recognition.Exact.EvenStandardType X := by
  rcases h with h | h | h
  · exact Or.inl ⟨.PSL, 2, 6, h.admissible, h⟩
  · exact Or.inl ⟨.PSU, 3, 3, h.admissible, h⟩
  · exact Or.inl ⟨.PSL, 3, 3, h.admissible, h⟩

theorem y6f4a_target_simple_nonab (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : Y6TargetLie X) : IsSimpleGroup X ∧ ¬ IsMulCommutative X := by
  have hS : IsSimpleGroup X := by
    rcases h with h | h | h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  refine ⟨hS, fun hc => ?_⟩
  haveI : IsSimpleGroup X := hS
  haveI : IsMulCommutative X := hc
  letI : CommGroup X := { (inferInstance : Group X) with
    mul_comm := fun a b => mul_comm' a b }
  have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card (α := X)
  rcases y6f4a_card_target hO h with h1 | h1 | h1
  · rw [h1] at hp
    exact absurd hp (by norm_num)
  · rw [h1] at hp
    exact absurd hp (by norm_num)
  · rw [h1] at hp
    exact absurd hp (by norm_num)

theorem y6f4a_exists_noncomm_of_not_comm {X : Type} [Group X] (h : ¬ IsMulCommutative X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push_neg at hc
  exact h (IsMulCommutative.of_comm hc)

theorem y6f4a_card_psl_two_four (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSL 2 2 2) : Nat.card X = 60 := by
  obtain ⟨-, h1, -⟩ := hO X .PSL 2 2 2 h.admissible h
  have hd : lieOrderDivisor .PSL 2 (2 ^ 2) = 1 := by decide +kernel
  have hn : lieOrderNumerator .PSL 2 (2 ^ 2) = 60 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem y6f4a_card_psl_three_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 1) : Nat.card X = 168 := by
  obtain ⟨-, h1, -⟩ := hO X .PSL 3 2 1 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .PSL 3 (2 ^ 1) = 168 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem y6f4a_card_psl_four_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSL 4 2 1) : Nat.card X = 20160 := by
  obtain ⟨-, h1, -⟩ := hO X .PSL 4 2 1 h.admissible h
  have hd : lieOrderDivisor .PSL 4 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .PSL 4 (2 ^ 1) = 20160 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem y6f4a_card_psu_four_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSU 4 2 1) : Nat.card X = 25920 := by
  obtain ⟨-, h1, -⟩ := hO X .PSU 4 2 1 h.admissible h
  have hd : lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem y6f4a_card_psl_three_four (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 2) : Nat.card X = 20160 := by
  obtain ⟨-, h1, -⟩ := hO X .PSL 3 2 2 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide +kernel
  have hn : lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by decide +kernel
  rw [hd, hn] at h1
  omega

theorem y6f4a_card_g2_four (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .G2 0 2 2) : Nat.card X = 251596800 := by
  obtain ⟨-, h1, -⟩ := hO X .G2 0 2 2 h.admissible h
  have hd : lieOrderDivisor .G2 0 (2 ^ 2) = 1 := by decide +kernel
  have hn : lieOrderNumerator .G2 0 (2 ^ 2) = 251596800 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem y6f4a_card_f4_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .F4 0 2 1) : Nat.card X = 3311126603366400 := by
  obtain ⟨-, h1, -⟩ := hO X .F4 0 2 1 h.admissible h
  have hd : lieOrderDivisor .F4 0 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .F4 0 (2 ^ 1) = 3311126603366400 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem y6f4a_card_twistedE6_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .twistedE6 0 2 1) : Nat.card X = 76532479683774853939200 := by
  obtain ⟨-, h1, -⟩ := hO X .twistedE6 0 2 1 h.admissible h
  have hd : lieOrderDivisor .twistedE6 0 (2 ^ 1) = 3 := by decide +kernel
  have hn : lieOrderNumerator .twistedE6 0 (2 ^ 1) = 229597439051324561817600 := by
    decide +kernel
  rw [hd, hn] at h1
  omega

theorem y6f4a_card_psp_three_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSp 3 2 1) : Nat.card X = 1451520 := by
  obtain ⟨-, h1, -⟩ := hO X .PSp 3 2 1 h.admissible h
  have hd : lieOrderDivisor .PSp 3 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .PSp 3 (2 ^ 1) = 1451520 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem y6f4a_card_psu_six_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSU 6 2 1) : Nat.card X = 9196830720 := by
  obtain ⟨-, h1, -⟩ := hO X .PSU 6 2 1 h.admissible h
  have hd : lieOrderDivisor .PSU 6 (2 ^ 1) = 3 := by decide +kernel
  have hn : lieOrderNumerator .PSU 6 (2 ^ 1) = 27590492160 := by decide +kernel
  rw [hd, hn] at h1
  omega

theorem y6f4a_card_pomegaPlus_eight_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .POmegaPlus 4 2 1) : Nat.card X = 174182400 := by
  obtain ⟨-, h1, -⟩ := hO X .POmegaPlus 4 2 1 h.admissible h
  have hd : lieOrderDivisor .POmegaPlus 4 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .POmegaPlus 4 (2 ^ 1) = 174182400 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem y6f4a_card_pomegaMinus_eight_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .POmegaMinus 4 2 1) : Nat.card X = 197406720 := by
  obtain ⟨-, h1, -⟩ := hO X .POmegaMinus 4 2 1 h.admissible h
  have hd : lieOrderDivisor .POmegaMinus 4 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .POmegaMinus 4 (2 ^ 1) = 197406720 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

end CFSG.OddStandard.HigherRank.YamadaG23
