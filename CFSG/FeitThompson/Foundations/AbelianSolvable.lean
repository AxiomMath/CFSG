module

public import Mathlib.GroupTheory.Solvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem commutator_eq_closure_inv_commutators (A B : Subgroup G) :
    ⁅A, B⁆ = Subgroup.closure {g | ∃ a ∈ A, ∃ b ∈ B, a⁻¹ * b⁻¹ * a * b = g} := by
  rw [Subgroup.commutator_def]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, commutatorElement_def]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by simp⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by simp⟩

theorem derivedSeries_one_eq_bot [IsMulCommutative G] : derivedSeries G 1 = ⊥ := by
  rw [derivedSeries_one, commutator_eq_bot]

theorem isSolvable_of_isMulCommutative [IsMulCommutative G] : Group.IsSolvable G :=
  (Group.isSolvable_def G).2 ⟨1, derivedSeries_one_eq_bot⟩

end CFSG.FeitThompson
