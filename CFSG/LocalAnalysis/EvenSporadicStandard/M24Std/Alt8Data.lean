module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G]

@[expose] def Alt8Data (L B : Subgroup G) : Prop :=
  ∃ φ : egNL L B →* alternatingGroup (Fin 8),
    Function.Surjective φ ∧ φ.ker = B.subgroupOf (egNL L B)

end CFSG.EvenSporadicStandard.M24Std
