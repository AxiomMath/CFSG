module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.Children

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard

@[expose] def ChildL34WAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G), StandardSetting G L → LieModel (L ⧸ center L) .PSL 3 2 2 →
    OddLieType G ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .ONan

@[expose] def ChildL34WHered : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Balance.UHered G → ChildL34WAt G

@[expose] def ChildHeWAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G), StandardSetting G L → IsSporadic (L ⧸ center L) .He → OddLieType G

@[expose] def ChildHeWHered : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Balance.UHered G → ChildHeWAt G

end CFSG.EvenSporadicStandard.Induction
