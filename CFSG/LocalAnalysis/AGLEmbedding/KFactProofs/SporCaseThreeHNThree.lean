module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate9506
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.HNThree


theorem sporCaseThreePrimeData_HN_three [Finite (NativeSporadic.Carrier .HN)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .HN) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.HN) (by norm_num)
    (tcGenDatum_of_check (specP 5 133) (D := tcSpec) Nat.prime_three
      Certificates.certificate9506.1)
    (coverPointDatum_of_check (specP 5 133) (D := cpSpec) Nat.prime_three
      Certificates.certificate9506.2.1 Certificates.certificate9506.2.2)

end CFSG.AGLEmbedding
