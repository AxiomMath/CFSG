module

public import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem commutator_eq_closure (H₁ H₂ : Subgroup G) :
    ⁅H₁, H₂⁆ = closure {g | ∃ a ∈ H₁, ∃ b ∈ H₂, a⁻¹ * b⁻¹ * a * b = g} := by
  rw [Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by group⟩

variable (G)

theorem map_subtype_derivedSeries_derivedSeries (i j : ℕ) :
    (derivedSeries (derivedSeries G i) j).map (derivedSeries G i).subtype
      = derivedSeries G (i + j) := by
  induction j with
  | zero => simp [← MonoidHom.range_eq_map]
  | succ j ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator, ih, ← derivedSeries_succ, ← add_assoc]

theorem mem_derivedSeries_add_iff {i j : ℕ} (x : G) :
    x ∈ derivedSeries G (i + j) ↔
      ∃ hx : x ∈ derivedSeries G i, (⟨x, hx⟩ : derivedSeries G i) ∈ derivedSeries _ j := by
  rw [← map_subtype_derivedSeries_derivedSeries G i j]
  simp [Subgroup.mem_map]

theorem derivedSeries_derivedSeries_eq_bot_iff (i j : ℕ) :
    derivedSeries (derivedSeries G i) j = ⊥ ↔ derivedSeries G (i + j) = ⊥ := by
  rw [← Subgroup.map_eq_bot_iff_of_injective _ (derivedSeries G i).subtype_injective,
    map_subtype_derivedSeries_derivedSeries]

theorem isSolvable_derivedSeries_iff (i : ℕ) :
    Group.IsSolvable (derivedSeries G i) ↔ ∃ j, derivedSeries G (i + j) = ⊥ := by
  simp [Group.isSolvable_def, derivedSeries_derivedSeries_eq_bot_iff]

end CFSG.FeitThompson
