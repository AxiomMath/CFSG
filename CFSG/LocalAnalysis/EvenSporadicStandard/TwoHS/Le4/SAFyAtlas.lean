module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def HSThreeClass : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E → Nat.card (center E) = 2 →
    IsSporadic (E ⧸ center E) .HS →
      (∀ a b : E, orderOf a = 3 → orderOf b = 3 → ∃ g : E, g * a * g⁻¹ = b) ∧
      (∀ a : E, orderOf a = 3 → Nat.card (centralizer ({a} : Set E)) ≤ 720)

@[expose] def HSInvolutionClasses : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E → Nat.card (center E) = 2 →
    IsSporadic (E ⧸ center E) .HS → ∀ z ∈ center E, z ≠ 1 →
      ∀ a b : E, a * a = 1 → b * b = 1 → a ∉ center E → b ∉ center E →
        ∃ g : E, g * a * g⁻¹ = b ∨ g * a * g⁻¹ = b * z

@[expose] def HSOuterThree : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (E : Subgroup H), IsHSCover H E → ∀ w : H, w * w = 1 →
    w ∉ E → ∃ r ∈ E, orderOf r = 3 ∧ r * w = w * r

end CFSG.EvenSporadicStandard.TwoHS
