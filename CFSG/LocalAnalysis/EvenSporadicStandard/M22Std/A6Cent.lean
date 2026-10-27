module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

@[expose] def a6CentCheck : Bool :=
  decide (∀ a : alternatingGroup (Fin 6), a * a = 1 →
    8 ∣ Fintype.card {b : alternatingGroup (Fin 6) // a * b = b * a})

end CFSG.EvenSporadicStandard.M22Std
