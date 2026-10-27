module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem global_invariant_two_maximal_is_maximal_within
    {G : Type*} [Group G] (actingGroup overgroup twoGroup : Subgroup G)
    (hmaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup)
    (hcontained : twoGroup ≤ overgroup) :
    invariantTwoMaximalWithin actingGroup overgroup twoGroup := by
  exact ⟨hcontained, hmaximal.1, hmaximal.2.1,
    fun larger _hle hgroup hinvariant hcontains => hmaximal.2.2 larger hgroup hinvariant hcontains⟩

end CFSG.RankThreeCoreUniqueness.Helpers
