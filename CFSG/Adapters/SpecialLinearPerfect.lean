module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ClassicalModels

open Matrix
open scoped commutatorElement

theorem transvection_mem_commutator_of_three_le
    {K : Type*} [Field K] {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ∈
      commutator (SpecialLinearGroup (Fin n) K) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  have hword :
      ⁅SpecialLinearGroup.transvection hki.symm c,
        SpecialLinearGroup.transvection hkj (1 : K)⁆ =
        SpecialLinearGroup.transvection hij c := by
    simpa only [mul_one] using
      SpecialLinearGroup.commutatorElement_transvection hki.symm hkj hij c (1 : K)
  rw [← hword]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem specialLinear_commutator_eq_top_of_three_le
    {K : Type*} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    commutator (SpecialLinearGroup (Fin n) K) = ⊤ := by
  apply le_antisymm le_top
  rw [← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin n) (K := K)]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  exact transvection_mem_commutator_of_three_le hn hij c

theorem specialLinear_isPerfect_of_three_le
    {K : Type*} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    Group.IsPerfect (SpecialLinearGroup (Fin n) K) :=
  ⟨specialLinear_commutator_eq_top_of_three_le hn⟩

theorem exists_ne_zero_sq_ne_one_of_four_le_card
    (K : Type*) [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  let _ := Fintype.ofFinite K
  by_contra h
  push Not at h
  have hsubset : (Finset.univ : Finset K) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have hs : a = 1 ∨ a = -1 := sq_eq_one_iff.mp (h a ha)
      rcases hs with rfl | rfl <;> simp
  have hbound := Finset.card_le_card hsubset
  have hsmall : ({0, 1, -1} : Finset K).card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (by simp)))
  have : Nat.card K ≤ 3 := by
    simpa only [Nat.card_eq_fintype_card, Finset.card_univ] using hbound.trans hsmall
  omega

theorem specialLinear_isPerfect_two_of_four_le_card
    (K : Type*) [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨a, ha, hs⟩ := exists_ne_zero_sq_ne_one_of_four_le_card K hK
  exact ⟨Matrix.SL2.commutator_eq_top ha hs⟩

end CFSG.ClassicalModels
