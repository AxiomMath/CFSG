module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.MainFull
public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.M11

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Blueprint.NativeSporadic

theorem m11Exclusion
    : M11Exclusion :=
  fun _ _ _ _ h => M11Std.m11_not_standard h

theorem largeExclusion_covers
    (G : Type) [Group G] [Finite G] (L : Subgroup G) (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) :
    ¬ IsSporadic (L ⧸ center L) .Ru ∧ ¬ IsSporadic (L ⧸ center L) .Co1 :=
  ⟨fun hQ => TwoRu.twoRu_not_standard_of_hypothesisOne h h2 hQ TwoRu.HypOne.hypothesisOne_native, fun hQ => TwoCo1.twoCo1_not_standard_full h h2 hQ⟩

end CFSG.EvenSporadicStandard
