module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.Bg.Iii2

@[expose] def FusionKlein : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    ∀ x y : G, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x ≠ y → x * y = y * x → x ∈ T → y ∈ T →
      (∀ t ∈ T, t * x = x * t) → IsConj x y →
      (∀ g : G, g * x * g⁻¹ ∈ T → g * x * g⁻¹ = x ∨ g * x * g⁻¹ = y ∨ g * x * g⁻¹ = x * y) →
        IsConj x (x * y)

end CFSG.GH74.GLS.Bg.Iii2
