module

public import CFSG.GH74.Uniqueness.Theorem1
public import CFSG.GH74.Uniqueness.Section4CoverRigid

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem benderFacts
    : BenderFacts := ⟨benderCoverRigid, benderOuterInvolution⟩

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.theorem1_unconditional
    (S : ZDSetup X Z M) :
    IsSimpleGroup X ∧ IsStronglyZEmbedded Z M ∧ (∃ z ∈ Z, Z = {y : X | IsConj z y}) ∧
      ∀ z ∈ Z, IsCentralInvolution z :=
  S.theorem1 benderFacts

end CFSG.GH74.Uniqueness
