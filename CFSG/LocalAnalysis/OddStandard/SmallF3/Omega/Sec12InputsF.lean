module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82StepFusionX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E X : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → Sec12X t S L E X →
      ∀ u ∈ X, u * u = 1 → u ≠ 1 → ∃ h : G, h⁻¹ * t * h = t * u

end CFSG.OddStandard.SmallF3.Omega
