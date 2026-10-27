module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Fink5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec7Ctx G t L S z →
    ∀ x ∈ S ⊓ centralizer (L : Set G), orderOf x = 4 →
      ∃ g : G, g⁻¹ * t * g ≠ t ∧ x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x

end CFSG.OddStandard.SmallF3.Omega
