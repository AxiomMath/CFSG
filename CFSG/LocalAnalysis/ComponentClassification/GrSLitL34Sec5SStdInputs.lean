module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def SuzONanFieldType (X : Type) [Group X] : Prop :=
  Blueprint.NativeSporadic.IsSporadic X .Suz ∨ Blueprint.NativeSporadic.IsSporadic X .ONan ∨
    ∃ n : ℕ, 4 ≤ n ∧ Even n ∧ Blueprint.LieModel X .PSL 3 2 n

@[expose] def SuzONanNotProperFixedCatalog : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup S, P ≤ fixedSubgroup σ → IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) →
      P ≠ ⊤ → ¬ Blueprint.NativeSporadic.IsSporadic (P ⧸ Open.fusionZStar P) .Suz ∧
        ¬ Blueprint.NativeSporadic.IsSporadic (P ⧸ Open.fusionZStar P) .ONan

@[expose] def L3TwoPowProperFixedCatalog : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ x y : S, x * y ≠ y * x) → Blueprint.Catalog S → ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup S, P ≤ fixedSubgroup σ → IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) →
      P ≠ ⊤ → Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 n →
        Blueprint.LieModel S .PSL 3 2 (2 * n)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
