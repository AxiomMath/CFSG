module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9418
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.Co3Three


theorem sporCaseThreePrimeData_Co3_three [Finite (NativeSporadic.Carrier .Co3)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Co3) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Co3) (by norm_num)
    (tcGenDatum_of_check (spec2 22) (D := tcSpec) Nat.prime_three
      Certificates.certificate9418.1)
    (coverPointDatum_of_check (spec2 22) (D := cpSpec) Nat.prime_three
      Certificates.certificate9418.2.1 Certificates.certificate9418.2.2)

end CFSG.AGLEmbedding
