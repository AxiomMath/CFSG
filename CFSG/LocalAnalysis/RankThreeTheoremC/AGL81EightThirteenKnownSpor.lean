module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeThThree
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Sporadic.Bridge.ThSurj
public import Certificates.Certificate9419

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Blueprint

theorem threeCoreAt_Co2 :
    ThreeCoreAt (TauCeti.CFSGIndex.sporadic .Co2).Group := by
  obtain ⟨e⟩ : Nonempty (NativeSporadic.Carrier .Co2 ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group) :=
    CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  refine threeCoreAt_of_tcGenDatum e ?_
  exact CFSG.AGLEmbedding.R3.tcGenDatum_of_check (CFSG.SectionRank.spec2 22)
    (D := CFSG.AGLEmbedding.R3.Co2Three.tcSpec) Nat.prime_three
    Certificates.certificate9419.1

theorem threeCoreAt_Th :
    ThreeCoreAt (TauCeti.CFSGIndex.sporadic .Th).Group := by
  obtain ⟨e⟩ : Nonempty (NativeSporadic.Carrier .Th ≃* (TauCeti.CFSGIndex.sporadic .Th).Group) :=
    CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  refine threeCoreAt_of_tcGenDatum e ?_
  exact CFSG.AGLEmbedding.tcGenDatum_Th_three

end CFSG.LocalAnalysis.RankThreeTheoremC
