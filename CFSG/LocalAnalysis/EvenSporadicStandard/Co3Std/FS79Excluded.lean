module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.Co3Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def FS79Co3Excluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → ¬ IsSporadic L .Co3

end CFSG.EvenSporadicStandard.Co3Std
