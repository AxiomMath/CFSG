module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem commutator_zpowers_eq_of_closure {G : Type*} [Group G] {X : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (X : Set G))
    (hX : Subgroup.closure {z : G | ∃ x ∈ X, z = ⁅x, b⁆} = X) :
    ⁅Subgroup.zpowers b, X⁆ = X := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_comm, ← Subgroup.le_normalizer_iff_commutator_le_left]
    exact Subgroup.zpowers_le.mpr hb
  · rw [← hX]
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨x, hx, rfl⟩
    have hmem : ⁅x, b⁆ ∈ ⁅X, Subgroup.zpowers b⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers b)
    rw [Subgroup.commutator_comm] at hmem
    simpa [hX] using hmem

end CFSG.GroupTheory

end
