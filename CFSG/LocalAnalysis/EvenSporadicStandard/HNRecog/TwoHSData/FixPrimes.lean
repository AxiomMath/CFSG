module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixPrime
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixFacts
public import Certificates.Certificate26775

public section

namespace CFSG.EvenSporadicStandard.HNRecog

section Cert


theorem fixFacts_P : FixFacts := Certificates.certificate26775

theorem trans_P : ∀ q : Fin 1408, ∃ g ∈ P1408, g q = 0 := fixFacts_P.trans

theorem primeFacts3 (hP : Nat.card ↥P1408 = 177408000) : PrimeFacts 3 [fix3] := fixFacts_P.p3 hP

theorem primeFacts5 (hP : Nat.card ↥P1408 = 177408000) : PrimeFacts 5 [fix5A, fix5B, fix5C] :=
  fixFacts_P.p5 hP

theorem primeFacts7 (hP : Nat.card ↥P1408 = 177408000) : PrimeFacts 7 [fix7] := fixFacts_P.p7 hP

end Cert

end CFSG.EvenSporadicStandard.HNRecog
