module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeC
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveTc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveCp
public import Certificates.Certificate9525

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.R3

section


theorem tcGenDatum_Ly_five :
    TCGenDatum NativeSporadic.Ly 5 :=
  tcGenDatum_of_ly5check (Dz := lyTzSpec5) Nat.prime_five Certificates.certificate9525

theorem coverPointDatum_Ly_five :
    CoverPointDatum NativeSporadic.Ly 5 :=
  coverPointDatum_of_ly5check (Dc := lyCzSpec5) Nat.prime_five Certificates.certificate9525

theorem sporCaseThreePrimeData_Ly_five
    [Finite (NativeSporadic.Carrier .Ly)] [Fact (Nat.Prime 5)] :
    SporCaseThreePrimeData (NativeSporadic.Carrier .Ly) 5 :=
  sporCaseThreePrimeData_of_tc_cp (X := NativeSporadic.Ly) (by norm_num) tcGenDatum_Ly_five
    coverPointDatum_Ly_five

end

end CFSG.AGLEmbedding
