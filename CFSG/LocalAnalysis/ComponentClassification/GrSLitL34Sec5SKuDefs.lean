module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def L34Sec5KuOddStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S,
    ∀ K₁ : Subgroup G, K₁ ≤ l34K L u → IsPComponent 2 (K₁.subgroupOf (l34K L u)) →
      ¬ oddIn L ⊓ K₁ ≤ oddIn K₁

end CFSG.ComponentClassification.GrSLit.GrS5S
