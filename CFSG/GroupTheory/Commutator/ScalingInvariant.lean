module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_of_forall_eq_commutatorElement {K S : Subgroup G} {g : G} (hg : g ∈ S)
    (hKg : ∀ y ∈ K, y * g * y⁻¹ ∈ S) (hK : ∀ x ∈ K, ∃ y ∈ K, x = ⁅y, g⁆) : K ≤ S := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hK x hx
  rw [commutatorElement_def]
  exact S.mul_mem (hKg y hy) (S.inv_mem hg)

end CFSG.GroupTheory
