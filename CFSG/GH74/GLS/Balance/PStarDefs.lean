module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def IsPStar (p : ℕ) (Y : Type*) [Group Y] : Prop :=
  oResidual p Y = ⊤ ∧ ∀ N : Subgroup Y, N.Normal → ∀ P : Sylow p ↥N,
    N ⊔ centralizer ((((P : Subgroup ↥N).map N.subtype : Subgroup Y)) : Set Y) = ⊤

@[expose] def BenderBalance : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Z N : Subgroup A) (x : A), orderOf x = 2 →
    x ∈ normalizer (Z : Set A) → N ≤ Z → (N.subgroupOf Z).Normal → IsPStar 2 ↥N →
      Z ≤ N ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set A) ⊓ Z) → IsPStar 2 ↥Z

end CFSG.GH74.GLS.Balance
