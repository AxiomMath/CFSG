module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem cyc_three {R : Type*} [Group R] [Finite R] [IsCyclic R] {x y : R} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) : x = 1 ∨ ∃ j : ℕ, y * x ^ j = 1 := by
  classical
  have := Fintype.ofFinite R
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  have hx2 : x ^ 2 ≠ 1 := fun h => hx1 (by
    have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
    rw [this, hx, h]; simp)
  have hxx : x ≠ x ^ 2 := fun h => hx1 (by
    have h3 : x * 1 = x * x := by rw [mul_one, ← pow_two]; exact h
    exact (mul_left_cancel h3).symm)
  set S : Finset R := Finset.univ.filter (fun a => a ^ 3 = 1) with hS
  have hcard : S.card ≤ 3 := IsCyclic.card_pow_eq_one_le (by norm_num)
  have hsub : ({1, x, x ^ 2} : Finset R) ⊆ S := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hx
    · rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
  have hc3 : ({1, x, x ^ 2} : Finset R).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hxx
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hx1 h.symm, fun h => hx2 h.symm⟩
  have heq : ({1, x, x ^ 2} : Finset R) = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hc3]; exact hcard)
  have hyS : y ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hy⟩
  rw [← heq] at hyS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyS
  rcases hyS with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨2, by rw [← pow_succ']; exact hx⟩
  · exact ⟨1, by rw [pow_one, ← pow_succ]; exact hx⟩

end CFSG.HardMathSupport.Solomon.Coordinator
