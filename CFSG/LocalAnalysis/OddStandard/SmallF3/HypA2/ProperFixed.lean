module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def ProperFixedComp {S : Type} [Group S] (σ : MulAut S) (P : Subgroup S) : Prop :=
  (∀ y, σ (σ y) = y) ∧ P ≤ fixedSubgroup σ ∧ P ≠ ⊤ ∧
    IsComponent (P.subgroupOf (fixedSubgroup σ))

end CFSG.OddStandard.SmallF3.HypA2
