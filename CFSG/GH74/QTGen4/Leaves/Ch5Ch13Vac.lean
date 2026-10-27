module

public import CFSG.GH74.QTGen4.Ch5.L34Offender
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs522
public import CFSG.GH74.QTGen4.Stmt1316
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1312Q
public import CFSG.GH74.QTGen4.A6.Gen4Cuts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS134Defs2

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.Blueprint

theorem stmt5_1_22_one_F4_holds :
    CFSG.Quasithin.H13.Stmt5_1_22_one_F4 := by
  intro G _ _ T M L V H B D D₃ Z₁ n h _ _ hL34 _ _ _ _
  exfalso
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  exact no_L34_modO2_of_inH (Finite4.gen4 (G := G)) h.qtke.2.1 P h.hStar.1 (oTwoUpper_le H) hL34

theorem u3LineComponentExclusionQ_F4_holds :
    CFSG.Quasithin.H13.U3.U3LineComponentExclusionQ_F4 := by
  intro G _ _ T L V z _ hH hL
  exact (not_lieModel_psu_three_three_of_gen4 (Finite4.gen4 (G := G)) hH hL).elim

theorem stmtEnd134_F4_holds :
    CFSG.Quasithin.H13.NQS134.StmtEnd134_F4 := by
  intro G _ _ T L V z h
  exact (false_of_setting134_gen4 (Finite4.gen4 (G := G)) h.S).elim

end CFSG.GH74.QTGen4.Leaves

