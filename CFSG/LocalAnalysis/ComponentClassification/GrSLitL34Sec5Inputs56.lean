module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L2UnbalancingSylowFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J P : Subgroup G), GSUnbalancingTriple a x J →
    (IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J)) →
    IsSylowTwoIn P J → ¬ P ≤ centralizer ({x} : Set G)

end CFSG.ComponentClassification.GrSLit
