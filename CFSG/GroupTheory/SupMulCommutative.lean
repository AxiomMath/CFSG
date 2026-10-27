module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem isMulCommutative_sup_of_elementwise_commute {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : IsMulCommutative ↥A) (hB : IsMulCommutative ↥B) :
    IsMulCommutative ↥(A ⊔ B) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure ?_
  intro x hx y hy _
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · exact congrArg Subtype.val (hA.is_comm.comm ⟨x, hxA⟩ ⟨y, hyA⟩)
  · exact h x hxA y hyB
  · exact (h y hyA x hxB).symm
  · exact congrArg Subtype.val (hB.is_comm.comm ⟨x, hxB⟩ ⟨y, hyB⟩)

end CFSG.GroupTheory
