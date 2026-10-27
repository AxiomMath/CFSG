module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open scoped commutatorElement

variable {C : Type*} [Group C]

abbrev qCenter (Q : Subgroup C) : Subgroup C := Q ⊓ Subgroup.centralizer (Q : Set C)

theorem mem_qCenter {Q : Subgroup C} {z : C} :
    z ∈ qCenter Q ↔ z ∈ Q ∧ ∀ x ∈ Q, x * z = z * x := by
  simp [qCenter, Subgroup.mem_centralizer_iff]

end CFSG.CGT.PushingUpLit.A78Sp4

