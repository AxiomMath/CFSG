module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Corollary

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem StdHyp.card_sylow_centralizer_eq_two (h : StdHyp G L)
    (hI : HypothesisOne (L ⧸ center L)) (hrank : 3 ≤ twoRank (L ⧸ center L))
    (h25 : Finkelstein77.Asc76Lemma25) (S : Sylow 2 (centralizer (L : Set G))) :
    Nat.card S = 2 :=
  Finkelstein77.card_sylow_eq_two_of_stdHyp h hI hrank h25 S

end CFSG.EvenSporadicStandard
