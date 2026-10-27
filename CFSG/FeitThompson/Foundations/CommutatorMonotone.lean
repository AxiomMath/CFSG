module

public import Mathlib.GroupTheory.Commutator.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem commutator_eq_closure_inv_mul_inv_mul_mul (A B : Subgroup G) :
    ⁅A, B⁆ = closure {g | ∃ a ∈ A, ∃ b ∈ B, a⁻¹ * b⁻¹ * a * b = g} := by
  rw [Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by simpa [commutatorElement_def] using h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by simpa [commutatorElement_def] using h⟩

end CFSG.FeitThompson

