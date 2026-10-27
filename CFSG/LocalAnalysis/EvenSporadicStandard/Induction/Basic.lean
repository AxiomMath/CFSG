module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.EvenSporadicStandard.Induction

abbrev GroupPred : Type 1 := ∀ (H : Type) [Group H] [Finite H], Prop

end CFSG.EvenSporadicStandard.Induction
