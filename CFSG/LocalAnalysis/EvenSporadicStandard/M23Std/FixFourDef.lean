module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

@[expose] def FixFour {G : Type} [Group G] (L F : Subgroup G) : Prop :=
  ∀ d ∈ normalizer (F : Set G) ⊓ L, d ∉ F → d * d ∈ F →
    Nat.card ↥(F ⊓ centralizer ({d} : Set G)) ≤ 4

end CFSG.EvenSporadicStandard.M23Std
