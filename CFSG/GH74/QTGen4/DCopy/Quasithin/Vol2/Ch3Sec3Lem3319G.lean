module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3318M
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3319C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3319F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Ln2D

public section
namespace CFSG.Quasithin.H13.L3319

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

theorem stmt3_3_19_of_F4
    (h14 : Stmt3_3_14_F4) (hGA : CFSG.Open.GriessAllModelsStatement) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) (h12 : Step3_3_12R_F4) (h15 : Step3_3_15R_F4)
    (hC34 : CFSG.Quasithin.C134L32Corr_F4)
    (h20 : Stmt3_3_20) (h51 : AsB51) (hI16 : AsI16Cover) :
    Stmt3_3_19_F4 := by
  intro G _ _ T M L D h
  refine ⟨fun e => ?_⟩
  have h18 := L3318.stmt3_3_18_of_F4 h14 hGA h38 h39 h12 h15 hC34 h20
  have hTL := L3318.le_normalizer_of_h14_F4 h14 h
  obtain ⟨hVc, hB, hcase⟩ := Ln2.module_cases_F4 h18 h51 hI16 h h38 h39 hTL (Or.inr rfl) e
  rcases hcase with ⟨Z, -, -, hZ, hext⟩ | hsnd
  · rw [hZ rfl] at hext
    exact false_of_extSq_F4 h h38 h39 h12 h14 hGA h51 e hB hext
  · exact false_of_sumNatDual_F4 h h38 h39 h12 hGA h51 hTL e hB hsnd

end CFSG.Quasithin.H13.L3319
