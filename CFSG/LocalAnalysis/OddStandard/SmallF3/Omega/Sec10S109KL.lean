module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Steps2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82StepKL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G)
    (g : G), Sec109Ctx G t L S z K1 K2 g →
    ∀ u ∈ secB S L, orderOf u = 2 → InducesTypeSome L u 5 1 2 (-1) →
      (∀ k : G, k⁻¹ * z * k ≠ u) → (∃ k : G, k⁻¹ * t * k = t * u) → False

end CFSG.OddStandard.SmallF3.Omega
