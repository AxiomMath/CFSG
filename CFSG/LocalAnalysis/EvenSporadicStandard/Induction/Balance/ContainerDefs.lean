module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Defs
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup

@[expose] def CatalogNoFixedDoubleCover : Prop :=
  ∀ k : ℕ, (k = 8 ∨ k = 11) → ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X) (t : X),
    CFSG.IsQuasisimple ↥K → IsPGroup 2 ↥(center ↥K) →
    CFSG.Blueprint.Catalog (↥K ⧸ center ↥K) → ¬ IsAltType (↥K ⧸ center ↥K) →
    orderOf t = 2 → t ∈ normalizer (K : Set X) → B ≤ K → B ≤ centralizer ({t} : Set X) →
    CFSG.GH74.GLS.IsDoubleCoverOfAlt ↥B k →
    (∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ∀ x ∈ K, z * x = x * z) →
    (B.subgroupOf (K ⊓ centralizer ({t} : Set X))).Normal → False

end CFSG.EvenSporadicStandard.Induction.Balance
