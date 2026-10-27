module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def HSMcLLyExclusionHered : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Induction.Balance.UHered G → ∀ L : Subgroup G, StdHyp G L →
    ¬ IsSporadic L .HS ∧ ¬ IsSporadic L .McL ∧ ¬ IsSporadic L .Ly

end CFSG.EvenSporadicStandard
