module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9417
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.McLThree


theorem sporCaseThreePrimeData_McL_three [Finite (NativeSporadic.Carrier .McL)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .McL) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.McL) (by norm_num)
    (tcGenDatum_of_check (spec3 21) (D := tcSpec) Nat.prime_three
      Certificates.certificate9417.1)
    (coverPointDatum_of_check (spec3 21) (D := cpSpec) Nat.prime_three
      Certificates.certificate9417.2.1 Certificates.certificate9417.2.2)

end CFSG.AGLEmbedding
