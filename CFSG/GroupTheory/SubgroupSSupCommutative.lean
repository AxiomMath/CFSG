module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G] {S : Set (Subgroup G)}

theorem isMulCommutative_sSup (hS : ∀ A ∈ S, ∀ B ∈ S, ⁅A, B⁆ = ⊥) :
    IsMulCommutative ↥(sSup S) := by
  have hcl : Subgroup.closure (⋃ A : S, (A : Set G)) = sSup S := by
    rw [sSup_eq_iSup']
    exact (Subgroup.iSup_eq_closure (fun A : S => (A : Subgroup G))).symm
  rw [← hcl]
  refine Subgroup.isMulCommutative_closure ?_
  intro x hx y hy _
  obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hx
  obtain ⟨B, hyB⟩ := Set.mem_iUnion.mp hy
  exact (Subgroup.mem_centralizer_iff.mp
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hS A A.2 B B.2)) hxA) y hyB).symm

end CFSG.GroupTheory

end
