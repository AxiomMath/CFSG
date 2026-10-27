module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9502
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.Co1Five


theorem sporCaseThreePrimeData_Co1_five [Finite (NativeSporadic.Carrier .Co1)]
    [Fact (Nat.Prime 5)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Co1) 5 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Co1) (by norm_num)
    (tcGenDatum_of_check (spec2 24) (D := tcSpec) Nat.prime_five
      Certificates.certificate9502.1)
    (coverPointDatum_of_check (spec2 24) (D := cpSpec) Nat.prime_five
      Certificates.certificate9502.2.1 Certificates.certificate9502.2.2)

end CFSG.AGLEmbedding
