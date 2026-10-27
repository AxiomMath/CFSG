module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

@[expose] def L34ProperFixedSimpleRank : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Blueprint.Catalog S → ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup S, P ≤ FixedCommutingProduct.fixedSubgroup σ →
      IsPComponent 2 (P.subgroupOf (FixedCommutingProduct.fixedSubgroup σ)) → P ≠ ⊤ →
      IsL34Type (P ⧸ Open.fusionZStar P) →
      Nonempty (S ≃* Blueprint.NativeSporadic.He) ∨ pRank 2 ↥(Open.fusionZStar P) ≤ 1

end CFSG.ComponentClassification.GrSLit
