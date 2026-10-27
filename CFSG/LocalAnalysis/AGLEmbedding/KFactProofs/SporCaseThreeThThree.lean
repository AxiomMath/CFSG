module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeTc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeCp
public import Certificates.Certificate9522
public import Certificates.Certificate9523

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3

section


theorem tcGenDatum_Th_three :
    TCGenDatum NativeSporadic.Th 3 :=
  tcGenDatum_of_zcheck (D := thTzSpec) Nat.prime_three Certificates.certificate9522

theorem coverPointDatum_Th_three :
    CoverPointDatum NativeSporadic.Th 3 :=
  coverPointDatum_of_zcheck (D := thCzSpec) Nat.prime_three Certificates.certificate9523

theorem sporCaseThreePrimeData_Th_three
    [Finite (NativeSporadic.Carrier .Th)] [Fact (Nat.Prime 3)] :
    SporCaseThreePrimeData (NativeSporadic.Carrier .Th) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Th) (by norm_num) tcGenDatum_Th_three
    coverPointDatum_Th_three

end

end CFSG.AGLEmbedding
