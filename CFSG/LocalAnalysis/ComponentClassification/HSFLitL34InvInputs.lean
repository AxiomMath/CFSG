module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS CFSG.ComponentClassification.GrSLit

@[expose] def L34Lemma55TypeStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ z ∈ S ⊓ coreActionKernel L, orderOf z = 2 →
    ∀ M : Subgroup G, M ≤ centralizer ({z} : Set G) →
      IsPComponent 2 (M.subgroupOf (centralizer ({z} : Set G))) → conjugate M t = M →
      gsFixedLayer L z ≤ M → IsL34Type (M ⧸ Open.fusionZStar M)

end CFSG.ComponentClassification.HSFLit.L34Inv
