module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.FiniteFactsHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Lemma210Holds
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Assembly.Recognition

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup

theorem fi24RecognitionLocal_of_pins_holds
    (hpins : ∀ {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G},
      Fi24Branch.Std G L E t → L.relIndex (centralizer ({t} : Set G)) = 2 →
      Nonempty (Pins G E t)) :
    Fi24RecognitionLocal :=
  fi24RecognitionLocal_of_pins CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
    Fi24Branch.ds81Lemma210Strong_holds Fi24Branch.finiteFacts_holds hpins

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
