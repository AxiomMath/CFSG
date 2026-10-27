module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.A9

open Equiv

@[expose] def A9Fact : Prop :=
  ∀ f : Perm (Fin 9), orderOf f = 5 → ∀ T : Subgroup (Perm (Fin 9)), IsPGroup 2 T →
    f ∈ Subgroup.normalizer (T : Set (Perm (Fin 9))) → ∀ t ∈ T, f * t = t * f

end CFSG.LocalAnalysis.GLTheoremA.S8.A9
