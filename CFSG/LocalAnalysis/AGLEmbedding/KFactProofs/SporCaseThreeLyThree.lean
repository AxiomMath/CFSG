module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeTc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeCp
public import Certificates.Certificate9524

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3

section


theorem tcGenDatum_Ly_three :
    TCGenDatum NativeSporadic.Ly 3 :=
  tcGenDatum_of_lycheck (Dz := lyTzSpec) Nat.prime_three Certificates.certificate9524

theorem coverPointDatum_Ly_three :
    CoverPointDatum NativeSporadic.Ly 3 :=
  coverPointDatum_of_lycheck (Dc := lyCzSpec) Nat.prime_three Certificates.certificate9524

theorem sporCaseThreePrimeData_Ly_three
    [Finite (NativeSporadic.Carrier .Ly)] [Fact (Nat.Prime 3)] :
    SporCaseThreePrimeData (NativeSporadic.Carrier .Ly) 3 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Ly) (by norm_num) tcGenDatum_Ly_three
    coverPointDatum_Ly_three

end

end CFSG.AGLEmbedding
