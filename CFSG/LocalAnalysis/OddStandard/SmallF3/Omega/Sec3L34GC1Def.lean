module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

structure L34GFac {A : Type} [Group A] (H : Subgroup A) (𝒮 : Set (Subgroup A)) (x : A) :
    Prop where
  le : ∀ S ∈ 𝒮, S ≤ H
  normal : ∀ S ∈ 𝒮, ∀ h ∈ H, ∀ s ∈ S, h * s * h⁻¹ ∈ S
  simple : ∀ S ∈ 𝒮, SimpleFStarQuotient ↥S
  comm : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → ∀ a ∈ S, ∀ b ∈ T, a * b = b * a
  sup_eq : sSup 𝒮 = H
  cent : centralizer (H : Set A) = ⊥
  invol : x * x = 1
  perm : ∀ S ∈ 𝒮, CFSG.conjugate S x ∈ 𝒮

end CFSG.OddStandard.SmallF3.Omega
