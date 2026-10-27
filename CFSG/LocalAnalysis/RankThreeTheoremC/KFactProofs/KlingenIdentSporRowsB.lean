module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeLyThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeLyFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeThThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoxeterB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux

open CFSG.Blueprint CFSG.AGLEmbedding

section Ly

theorem genData_Ly_three
    [Finite (NativeSporadic.Carrier .Ly)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Ly) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Ly) (by norm_num) tcGenDatum_Ly_three
    coverPointDatum_Ly_three

theorem genData_Ly_five [Finite (NativeSporadic.Carrier .Ly)]
    [Fact (Nat.Prime 5)] : GenData (NativeSporadic.Carrier .Ly) 5 :=
  genData_of_tc_cp (X := NativeSporadic.Ly) (by norm_num) tcGenDatum_Ly_five
    coverPointDatum_Ly_five

end Ly

section Th

theorem genData_Th_three
    [Finite (NativeSporadic.Carrier .Th)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Th) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Th) (by norm_num) tcGenDatum_Th_three
    coverPointDatum_Th_three

end Th

section B

theorem genData_B_three [Finite (NativeSporadic.Carrier .B)] [Fact (Nat.Prime 3)]
    (hc : 2 < Nat.card (NativeSporadic.Carrier .B)) : GenData (NativeSporadic.Carrier .B) 3 :=
  genData_of_tc_cp (X := NativeSporadic.B) (by norm_num)
    (CFSG.AGLEmbedding.BCox.tcGenDatum_B_three hc)
    (CFSG.AGLEmbedding.BCox.coverPointDatum_B_three hc)

end B

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
