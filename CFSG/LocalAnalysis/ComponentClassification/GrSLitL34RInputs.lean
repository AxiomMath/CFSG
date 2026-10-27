module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def EvenLieExcOuterL34Input : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (τ : StatedLieTag) (n f : ℕ),
    (τ, n, f) ∈ [(.PSU, 6, 1), (.POmegaPlus, 4, 1)] → Blueprint.LieModel S τ n 2 f →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ P : Subgroup (fixedSubgroup σ), IsPComponent 2 P → ¬ IsL34Type (P ⧸ Open.fusionZStar P)

@[expose] def SuzDoubleCoverL34Input : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → IsPGroup 2 (center Q) →
    center Q ≠ ⊥ → Nonempty (Q ⧸ center Q ≃* Blueprint.NativeSporadic.Carrier .Suz) →
    ∀ σ : MulAut Q, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup Q, P ≤ fixedSubgroup σ →
      IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) → P ≠ ⊤ →
      IsL34Type (P ⧸ Open.fusionZStar P) → pRank 2 ↥(Open.fusionZStar P) ≤ 1

end CFSG.ComponentClassification.GrSLit
