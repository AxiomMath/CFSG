module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.Induction.CoverFix

open Subgroup

theorem exists_elemAbelian_four {X : Type*} [Group X] [Finite X] {F : Subgroup X} {u z : X}
    (huF : u ∈ F) (hzF : z ∈ F) (hu : u * u = 1) (hz : z * z = 1) (huz : u * z = z * u)
    (hu1 : u ≠ 1) (hz1 : z ≠ 1) (hne : u ≠ z) :
    ∃ E : Subgroup X, E ≤ F ∧ (∀ e ∈ E, e * e = 1) ∧
      (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) ∧ 4 ≤ Nat.card E := by
  classical
  set E : Subgroup X := closure ({u, z} : Set X) with hE
  have huE : u ∈ E := subset_closure (Set.mem_insert _ _)
  have hzE : z ∈ E := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hcomm : IsMulCommutative ↥E := by
    refine Subgroup.isMulCommutative_closure ?_
    intro x hx y hy _
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · rfl
      · rw [Set.mem_singleton_iff.1 hy]
        exact huz
    · rcases hy with rfl | hy
      · rw [Set.mem_singleton_iff.1 hx]
        exact huz.symm
      · rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]
  have hcommE : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf => by
    have := (IsMulCommutative.is_comm (M := ↥E)).comm ⟨e, he⟩ ⟨f, hf⟩
    simpa using congrArg Subtype.val this
  have hsq : ∀ e ∈ E, e * e = 1 := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with rfl | hs
      · exact hu
      · rw [Set.mem_singleton_iff.1 hs]
        exact hz
    | one => simp
    | mul a b ha hb iha ihb =>
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcommE b hb a ha]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  have huz1 : u * z ≠ 1 := by
    intro h
    apply hne
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hz]
  have hcard : 4 ≤ Nat.card E := by
    have hsub : ({1, u, z, u * z} : Set X) ⊆ (E : Set X) := by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact E.one_mem
      · exact huE
      · exact hzE
      · exact E.mul_mem huE hzE
    have nuz : u ≠ u * z := fun h => hz1 (mul_left_cancel (a := u) (b := z) (c := 1) (by
      rw [mul_one]
      exact h.symm))
    have nzz : z ≠ u * z := fun h => hu1 (mul_right_cancel (a := u) (b := z) (c := 1) (by
      rw [one_mul]
      exact h.symm))
    have n2 : u ∉ ({z, u * z} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, nuz⟩
    have n3 : (1 : X) ∉ ({u, z, u * z} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hu1.symm, hz1.symm, huz1.symm⟩
    have h1 : ({1, u, z, u * z} : Set X).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem n3, Set.ncard_insert_of_notMem n2, Set.ncard_pair nzz]
    calc 4 = ({1, u, z, u * z} : Set X).ncard := h1.symm
      _ ≤ (E : Set X).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card E := (Nat.card_coe_set_eq (E : Set X)).symm
  have hEF : E ≤ F := by
    rw [hE, closure_le]
    rintro _ (rfl | hx)
    · exact huF
    · rw [Set.mem_singleton_iff.1 hx]
      exact hzF
  exact ⟨E, hEF, hsq, hcommE, hcard⟩

end CFSG.EvenSporadicStandard.Induction.CoverFix
