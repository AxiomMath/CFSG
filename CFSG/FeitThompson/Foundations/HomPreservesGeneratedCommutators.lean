module
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G K : Type*} [Group G] [Group K]

theorem closure_setOf_inv_mul_inv_mul_mul (A B : Subgroup G) :
    Subgroup.closure {g : G | ∃ a ∈ A, ∃ b ∈ B, a⁻¹ * b⁻¹ * a * b = g} = ⁅A, B⁆ := by
  rw [Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by group⟩

theorem map_closure_setOf_inv_mul_inv_mul_mul (f : G →* K) (A B : Subgroup G) :
    Subgroup.map f (Subgroup.closure {g : G | ∃ a ∈ A, ∃ b ∈ B, a⁻¹ * b⁻¹ * a * b = g}) =
      Subgroup.closure {g : K | ∃ a ∈ A.map f, ∃ b ∈ B.map f, a⁻¹ * b⁻¹ * a * b = g} := by
  rw [closure_setOf_inv_mul_inv_mul_mul, closure_setOf_inv_mul_inv_mul_mul,
    Subgroup.map_commutator]

end CFSG.FeitThompson
