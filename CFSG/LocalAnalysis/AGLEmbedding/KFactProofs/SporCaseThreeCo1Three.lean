module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9503
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.Co1Three


theorem sporCaseThreePrimeData_Co1_three [Finite (NativeSporadic.Carrier .Co1)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Co1) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Co1) (by norm_num)
    (tcGenDatum_of_check (spec2 24) (D := tcSpec) Nat.prime_three
      Certificates.certificate9503.1)
    (coverPointDatum_of_check (spec2 24) (D := cpSpec) Nat.prime_three
      Certificates.certificate9503.2.1 Certificates.certificate9503.2.2)

end CFSG.AGLEmbedding
