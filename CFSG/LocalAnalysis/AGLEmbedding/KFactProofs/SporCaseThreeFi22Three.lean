module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9501
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.Fi22Three


theorem sporCaseThreePrimeData_Fi22_three [Finite (NativeSporadic.Carrier .Fi22)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Fi22) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Fi22) (by norm_num)
    (tcGenDatum_of_check (spec3 77) (D := tcSpec) Nat.prime_three
      Certificates.certificate9501.1)
    (coverPointDatum_of_check (spec3 77) (D := cpSpec) Nat.prime_three
      Certificates.certificate9501.2.1 Certificates.certificate9501.2.2)

end CFSG.AGLEmbedding
