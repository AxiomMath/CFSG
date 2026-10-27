module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzShape
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def FritzFusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho tau : G) (T₂ : Subgroup G) (a₁₂ a₂₂ a₃₂ : G),
    Ctx t L S x₁ x₂ lam rho tau → Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → FzSylow T₂ →
    FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ →
    ∀ a ∈ fzR3 t x₁ x₂ a₃₂, ∀ g ∈ centralizer ({(x₁ * x₂) ^ 2} : Set G),
      g * a * g⁻¹ ∈ T₂ → g * a * g⁻¹ ∈ fzR3 t x₁ x₂ a₃₂

@[expose] def FritzCtxInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G),
    Ctx0 t L S x₁ x₂ lam rho → invCent t ≠ twoCore t ⊔ L →
    ∃ tau : G, Ctx t L S x₁ x₂ lam rho tau

end CFSG.OddStandard.SmallF3.FritzII
