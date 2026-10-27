module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9504
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.ONThree


theorem sporCaseThreePrimeData_ON_three [Finite (NativeSporadic.Carrier .ONan)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .ONan) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.ON) (by norm_num)
    (tcGenDatum_of_check (spec3 154) (D := tcSpec) Nat.prime_three
      Certificates.certificate9504.1)
    (coverPointDatum_of_check (spec3 154) (D := cpSpec) Nat.prime_three
      Certificates.certificate9504.2.1 Certificates.certificate9504.2.2)

end CFSG.AGLEmbedding
