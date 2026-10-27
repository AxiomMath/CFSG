module

public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint CFSG.GH74 CFSG.GH74.Generic

structure E2ComponentFacts : Prop where
  noTwoCover_even : ∀ (S : Type) [Group S],
    (LieModel S .PSL 2 2 3 ∨ LieModel S .PSL 2 2 4 ∨ LieModel S .PSU 3 2 2) → NoTwoCover S
  l34_cover : ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    LieModel (K ⧸ center K) .PSL 3 2 2 → center K ≠ ⊥ → Monoid.exponent ↥(center K) ≠ 4 →
      ¬ Gen4 K
  sz8_cover : ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    LieModel (K ⧸ center K) .twistedB2 0 2 3 → Nat.card (center K) ≤ 2 ∨ ¬ Gen4 K
  m12_cover : ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    NativeSporadic.IsSporadic (K ⧸ center K) .M12 → Nat.card (center K) ≤ 2
  noTwoCover_sporadic : ∀ (S : Type) [Group S], NativeSporadic.IsSporadic S .M11 → NoTwoCover S
  cover_not_gen4 : ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    (NativeSporadic.IsSporadic (K ⧸ center K) .M22 ∨
      NativeSporadic.IsSporadic (K ⧸ center K) .J2) → center K ≠ ⊥ → ¬ Gen4 K
  cover_not_gen4_M23_J3 : ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K →
    IsPGroup 2 ↥(center K) → (NativeSporadic.IsSporadic (K ⧸ center K) .M23 ∨
      NativeSporadic.IsSporadic (K ⧸ center K) .J3) → center K ≠ ⊥ → ¬ Gen4 K

end CFSG.GH74.E2
