module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import Certificates.Certificate9509
public import Certificates.Certificate9510
public import Certificates.Certificate9511
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MatOpsChecks
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.Fi24Three


theorem sporCaseThreePrimeData_Fi24_three [Finite (NativeSporadic.Carrier .Fi24Prime)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Fi24Prime) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Fi24prime) (by norm_num)
    (tcGenDatum_of_check (CFSG.RankThree.Asc83Table.matOpsSpec 3 781) (D := tcSpec)
      Nat.prime_three (tcCheck_matOps 170 Certificates.certificate9509
        Certificates.certificate9510))
    (coverPointDatum_of_check (CFSG.RankThree.Asc83Table.matOpsSpec 3 781) (D := cpSpec)
      Nat.prime_three (cpCheck_matOps Certificates.certificate9511.1)
      Certificates.certificate9511.2)

end CFSG.AGLEmbedding
