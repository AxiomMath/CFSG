module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

@[expose] def Sec4FOdd (H : Subgroup G) : Subgroup G :=
  (oddCore ↥H).map H.subtype

@[expose] def Sec4FOddCent (O E : Subgroup G) : Prop :=
  (∀ o ∈ O, ∀ x ∈ E, o * x = x * o) ∧ Odd (Nat.card O)

end CFSG.OddStandard.SmallF3.Omega
