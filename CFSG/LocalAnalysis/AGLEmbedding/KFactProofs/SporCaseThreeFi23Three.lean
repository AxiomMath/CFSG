module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9507
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.Fi23Three


theorem sporCaseThreePrimeData_Fi23_three [Finite (NativeSporadic.Carrier .Fi23)]
    [Fact (Nat.Prime 3)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Fi23) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Fi23) (by norm_num)
    (tcGenDatum_of_check (spec3 253) (D := tcSpec) Nat.prime_three
      Certificates.certificate9507.1)
    (coverPointDatum_of_check (spec3 253) (D := cpSpec) Nat.prime_three
      Certificates.certificate9507.2.1 Certificates.certificate9507.2.2)

end CFSG.AGLEmbedding
