module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def KKFuse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z : G),
    Hyp23 Ω K K' z → ∀ u₁ u₂ : G, u₁ ∈ K ⊔ K' → u₁ ≠ 1 → u₁ ≠ z → u₁ * u₁ = 1 →
      u₂ ∈ K ⊔ K' → u₂ ≠ 1 → u₂ ≠ z → u₂ * u₂ = 1 →
        ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * u₁ * c⁻¹ = u₂

end Asc77

end CFSG.ClassicalInvolution.Q8P
