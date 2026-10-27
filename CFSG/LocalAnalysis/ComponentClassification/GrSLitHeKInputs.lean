module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

@[expose] def L34RankTwoCentralFixedInput : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → IsPGroup 2 (center Q) →
    Blueprint.Catalog (Q ⧸ center Q) → ∀ σ : MulAut Q, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup Q, P ≤ FixedCommutingProduct.fixedSubgroup σ →
      IsPComponent 2 (P.subgroupOf (FixedCommutingProduct.fixedSubgroup σ)) → P ≠ ⊤ →
      IsL34Type (P ⧸ Open.fusionZStar P) → 2 ≤ pRank 2 ↥(Open.fusionZStar P) →
      ∀ z ∈ P, z ∈ center Q → z ≠ 1 → False

end CFSG.ComponentClassification.GrSLit
