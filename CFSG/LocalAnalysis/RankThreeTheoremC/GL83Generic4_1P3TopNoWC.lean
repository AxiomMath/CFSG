module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6AutData
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28PartsS
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28WCDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlanesA6U3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlanesM11L34
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Lem42
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Shared43
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6WC
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28WC
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3WC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem genericPrimeThree_of_kfacts_nowc (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) (hno : NoExcludedSection3 G)
    (hL : KFactsL34Full) (hU : KFactU3TwoSignalizer) (hA1 : KFactA6TwoSignalizer)
    (hA2 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE2 : KFactL28FieldSignalizer) (hE3 : KFactL28BorelCore) (hAct : KFactA6SylowAction)
    (hUAct : KFactU3SylowInversion) (hAut : A6AutData) (hInv : L28SylowInversion)
    (h43 : GL83GenericPrimeThreeLemma43 G) (hU43 : GL83GenericPrimeThreeU3Lemma43 G)
    (hA43 : GL83GenericPrimeThreeA6Lemma43 G) (hE34 : GL83GenericPrimeThreeL28Prop34SNoWC G)
    (hE43 : GL83GenericPrimeThreeL28Lemma43S G) (hNA : GL83Generic4_9BNonabS G)
    (hrem : GL83GenericPrimeThreeL34Remark G) :
    GL83GenericPrimeThree G :=
  have hU34 : GL83GenericPrimeThreeU3Fusion G :=
    .of_kfacts hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA2 hA3 hE1 hE3 hUAct
  have hA34 : GL83GenericPrimeThreeA6Prop34 G :=
    .of_kfacts hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA2 hA3 hE1 hE3 hAct hAut
  have hE34S : GL83GenericPrimeThreeL28Prop34S G :=
    .of_nowc hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA2 hA3 hE1 hE3 hInv hE34
  genericPrimeThree_of_types4_of_kfacts hS hU0 hD1 K1 K2 K3 K4 hInn hWC hKM hKA hKT hSig hno
    (.of_three
      (.of_two
        (.of_a6_l28
          (.of_planes hS hU0 hD1 hInn hWC K1 K2 K3 K4 hno hKM hKA hKT hSig hL hA2 hA1 hA3 hE1 hE3
            hAct hU34 hE34S hA34 hA43)
          (.of_partsS hS hU0 hD1 hInn hWC hE1 hE2 hE3 hE34S
            (.of_prop34S hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA2 hA3 hE1 hE3 hE34S) hE43 hNA))
        (.of_planes hS hU0 hD1 hInn hWC K1 K2 K3 K4 hno hKM hKA hKT hSig hL hA2 hA3 hE1 hE3 hAct
          hUAct hA34 hE34S u3SylowData_proved hU u3BorelCore_proved u3AutData_proved hU34 hU43))
      (.of_parts hS hU0 hD1 hInn hWC hL.twoSignalizer hL.three hL.unitary hL.borel hL.graph
        hL.outThree hL.sylowCentralizer hL.threeExponent (.of_kfacts hS hU0 hD1 hSig hL)
        (.of_planes hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA2 hA3 hE1 hE3) h43.toL34 hrem))
    (.of_planes hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hKT hL hA2 hA3 hE1 hE3) h43.toM11

end CFSG.LocalAnalysis.RankThreeTheoremC
