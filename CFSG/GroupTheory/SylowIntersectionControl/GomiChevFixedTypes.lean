module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools Subgroup

@[expose] def GomiChevFixedTypes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L I U : Subgroup G), IsGomiChevTwo ↥L →
    ¬ (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨ IsGomiSz (↥L ⧸ center ↥L)) →
    IsPGroup 2 I → I ≤ normalizer (L : Set G) → IsSylowOf 2 U L →
    I ≤ normalizer (U : Set G) →
    (∀ A : Subgroup G, IsGomiAtom L U A → (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) ≠ L) →
    ¬ IsPIsolatedOver 2 (L ⊓ centralizer (I : Set G)) ⊥

end CFSG.GroupTheory
