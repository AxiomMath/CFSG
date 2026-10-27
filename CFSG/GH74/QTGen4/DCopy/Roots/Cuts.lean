module

public import CFSG.GH74.QTGen4.Stmt1316
public import CFSG.GH74.QTGen4.A5.Gen4Cuts
public import CFSG.GH74.QTGen4.L32.Gen4Cuts
public import CFSG.GH74.QTGen4.Leaves.KGFactVac
public import CFSG.GH74.QTGen4.Ch6.Res614Tits
public import CFSG.GH74.QTGen4.Core.Stmt1001Gen4
public import CFSG.GH74.QTGen4.Core.Stmt1101Gen4
public import CFSG.GH74.QTGen4.Core.Stmt1211Vac
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622F4L45C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems14324
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem4TB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs523
public import CFSG.GH74.QTGen4.Leaves.Setting147Three
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1

public section

namespace CFSG.GH74.QTGen4.DCopy.Roots

open CFSG.GH74.QTGen4 CFSG.Quasithin CFSG.Quasithin.H13

theorem c134Case4Lemma45Corr_F4_holds : CFSG.Quasithin.H13.A5.C134Case4Lemma45Corr_F4 :=
  fun G _ _ => c134Case4Lemma45Corr_gen4_holds G Finite4.gen4

theorem case1442FromConcl13S_F4_holds : CFSG.Quasithin.H13.Case1442FromConcl13S_F4 := by
  intro G _ _ T L V V₂ g a D C _
  have h := finrank_hatModel_le_four (Finite4.gen4 (G := G)) D
  obtain ⟨k, hk, h3⟩ := C.dim
  omega

theorem case1442FromConcl9_F4_holds : CFSG.Quasithin.H13.Case1442FromConcl9_F4 := by
  intro G _ _ T L V V₂ g a D C _
  have h := finrank_hatModel_le_four (Finite4.gen4 (G := G)) D
  obtain ⟨k, hk, h3⟩ := C.dim
  omega

theorem asc94_M24He_L52Type_F4_holds : CFSG.Quasithin.H13.Asc94_M24He_L52Type_F4 :=
  fun G _ _ => Leaves.KGFactVac.asc94_M24He_L52Type_gen4 G Finite4.gen4

theorem lemma14324Big_F4_holds : CFSG.Quasithin.H13.Lemma14324Big_F4 :=
  fun G _ _ => lemma14324Big_gen4 G Finite4.gen4

theorem res614TitsCore_F4_holds :
    CFSG.Quasithin.H13.Res614TitsCore_F4 :=
  fun G _ _ => res614TitsCore_gen4 G Finite4.gen4

theorem stmt10_0_1_F4_holds : CFSG.Quasithin.H13.Stmt10_0_1_F4 :=
  fun G _ _ => stmt10_0_1_gen4 G Finite4.gen4

theorem stmt11_0_1_F4_holds :
    CFSG.Quasithin.H13.Stmt11_0_1_F4 :=
  fun G _ _ => stmt11_0_1_gen4 G Finite4.gen4

theorem stmt12_1_11_F4_holds : CFSG.Quasithin.H13.Stmt12_1_11_F4 :=
  fun G _ _ => stmt12_1_11_gen4 G Finite4.gen4

theorem stmt13_1_7_F4_holds : CFSG.Quasithin.H13.Stmt13_1_7_F4 :=
  fun G _ _ => stmt13_1_7_gen4 G Finite4.gen4

theorem stmt13_3_16_F4_holds : CFSG.Quasithin.H13.Stmt13_3_16_F4 :=
  fun G _ _ _ _ hH => not_lieModel_psu_three_three_of_gen4 (Finite4.gen4 (G := G)) hH

theorem stmt5_1_23_offender_F4_holds :
    CFSG.Quasithin.H13.Stmt5_1_23_offender_F4 :=
  fun G _ _ => stmt5_1_23_offender_gen4 G Finite4.gen4

theorem thm14_7_14_F4_holds : CFSG.Quasithin.H13.Thm14_7_14_F4 :=
  fun G _ _ _ _ _ _ S h3 => false_of_setting147_three (Finite4.gen4 (G := G)) S h3

end CFSG.GH74.QTGen4.DCopy.Roots
