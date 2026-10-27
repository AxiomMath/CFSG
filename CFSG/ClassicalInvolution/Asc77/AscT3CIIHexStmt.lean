module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIStmt

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def OmegaNbrTwin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K J : Subgroup G) (z t a g : G),
    CaseIIHyp p f K J z t a g →
      ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K

variable {p f}

structure Hex20 {G : Type} [Group G] (Ω : Set (Subgroup G)) (K J W : Subgroup G) : Prop where
  JW : J ⊓ W ∈ USet Ω
  hW : W = (W ⊓ K) ⊔ (W ⊓ J)

variable (p f)

@[expose] def HexAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Hex20 (CoreAssembly.conjClass K) K J W

end CFSG.ClassicalInvolution.Asc77.T3CII
