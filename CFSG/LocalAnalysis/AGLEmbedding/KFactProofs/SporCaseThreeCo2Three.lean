module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9419
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.Co2Three


theorem sporCaseThreePrimeData_Co2_three [Finite (NativeSporadic.Carrier .Co2)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Co2) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Co2) (by norm_num)
    (tcGenDatum_of_check (spec2 22) (D := tcSpec) Nat.prime_three
      Certificates.certificate9419.1)
    (coverPointDatum_of_check (spec2 22) (D := cpSpec) Nat.prime_three
      Certificates.certificate9419.2.1 Certificates.certificate9419.2.2)

end CFSG.AGLEmbedding
