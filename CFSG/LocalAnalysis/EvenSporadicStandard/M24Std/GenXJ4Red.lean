module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Final4
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXJ4

public section

namespace CFSG.EvenSporadicStandard.M24Std.GenX

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem j4_not_standard_of_secondHalfRed {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hA : Ega81HypAZ2A8K) (hHS : HarrisSolomonZ2S6IsoK) (h2 : Ega81Lemmas214to217Red)
    (h : StdHyp G L) : ¬ IsSporadic L .J4 :=
  J4Std.j4_not_standard hA (ega81M24Section_of_secondHalf' hHS (ega81Lemmas214to217_of_red h2)) h

end CFSG.EvenSporadicStandard.M24Std.GenX
