module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.OddIndexThree

variable {G : Type*} [Group G]

def fixedSubgroup (a : G ≃* G) : Subgroup G :=
  a.toMonoidHom.eqLocus (MonoidHom.id G)

@[simp] theorem mem_fixedSubgroup (a : G ≃* G) (x : G) :
    x ∈ fixedSubgroup a ↔ a x = x := Iff.rfl

variable [Finite G]

end CFSG.OddIndexThree
