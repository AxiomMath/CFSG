module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup

@[expose] def FixedRootRankOne {D : Type*} [Group D] (α : MulAut D) (S : Subgroup D) : Prop :=
  ∀ P : Subgroup D, P ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D) →
    IsPGroup 2 P → Nat.card P ≤ 2 ∧ (α ∉ (MulAut.conj : D →* MulAut D).range → P = ⊥)

end CFSG.LocalAnalysis.EvenBN.GMSK
