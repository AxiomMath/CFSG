module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate9505
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.HNFive


theorem sporCaseThreePrimeData_HN_five [Finite (NativeSporadic.Carrier .HN)]
    [Fact (Nat.Prime 5)] : SporCaseThreePrimeData (NativeSporadic.Carrier .HN) 5 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.HN) (by norm_num)
    (tcGenDatum_of_check (specP 5 133) (D := tcSpec) Nat.prime_five
      Certificates.certificate9505.1)
    (coverPointDatum_of_check (specP 5 133) (D := cpSpec) Nat.prime_five
      Certificates.certificate9505.2.1 Certificates.certificate9505.2.2)

end CFSG.AGLEmbedding
