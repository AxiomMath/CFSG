module

public import Certificates.Data.Kernel.K1471PermTab
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.K1471PermTab

open scoped commutatorElement

variable {n : ℕ}

@[simp] theorem length_tab (p : Equiv.Perm (Fin n)) : (tab p).length = n := by
  simp [tab]

end CFSG.KC.K1471PermTab

end
