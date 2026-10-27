module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieMain
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporOut

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCarrierOutOdd_holds
    : SporadicCarrierOutOdd := by
  intro s p hp hp2 T _ ⟨e⟩
  obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  have h1 := CFSG.LocalAnalysis.RankFourTheoremC.sporadicOutOdd_holds s p hp hp2
  rwa [← Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence (e.trans e')).toEquiv] at h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
