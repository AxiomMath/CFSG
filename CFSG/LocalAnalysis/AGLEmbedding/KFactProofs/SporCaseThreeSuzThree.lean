module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9500
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.SuzThree


theorem sporCaseThreePrimeData_Suz_three [Finite (NativeSporadic.Carrier .Suz)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Suz) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Suz) (by norm_num)
    (tcGenDatum_of_check (spec3 64) (D := tcSpec) Nat.prime_three
      Certificates.certificate9500.1)
    (coverPointDatum_of_check (spec3 64) (D := cpSpec) Nat.prime_three
      Certificates.certificate9500.2.1 Certificates.certificate9500.2.2)

end CFSG.AGLEmbedding
