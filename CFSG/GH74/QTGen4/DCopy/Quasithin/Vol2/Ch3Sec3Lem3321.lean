module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321D
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FH
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FSD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321GExt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321GT
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Ln2D

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace L3321

theorem step3_3_21f_of_F4 (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h14 : Stmt3_3_14_F4)
    (hGA : GriessAllModelsStatement) (he : Step3_3_21e_F4) (h15 : Step3_3_15R_F4)
    (hC34 : CFSG.Quasithin.C134L32Corr_F4)
    (h12 : Step3_3_12R_F4) (h20 : Stmt3_3_20) (hd : Step3_3_21d_F4)
    (hfQ : Step3_3_21fQ_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
      Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
      Mod3321 T L → ¬ InducesInnerOn T L := by
  intro G _ _ T M L D h ⟨e⟩ ⟨_, hmod⟩ hin
  rcases hmod with hext | hsum
  · exact false_of_inner_ext_F4 h7 h9 h14 hGA he h15 hC34 h20 hd hfQ h e hext hin
  · exact false_of_inner_sum_of_h12_F4 h7 h14 hGA he h15 hC34 h12 h e hsum hin

end L3321

theorem stmt3_3_21_of_F4
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h13 : Stmt3_3_13LT_F4) (h14 : Stmt3_3_14_F4)
    (h18 : Stmt3_3_18_F4) (h20 : Stmt3_3_20) (h51 : AsB51) (hI16 : AsI16Cover)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hGA : GriessAllModelsStatement)
    (h15 : Step3_3_15R_F4) (hC34 : CFSG.Quasithin.C134L32Corr_F4)
    (h12 : Step3_3_12R_F4) (hfQ : Step3_3_21fQ_F4) :
    Stmt3_3_21_F4 := by
  intro G _ _ T M L D h
  refine ⟨fun e => ?_⟩
  obtain ⟨-, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hab, -, hmod⟩ := Ln2.module_cases_F4 h18 h51 hI16 h h38 h39 hTL (Or.inl rfl) e
  have hd := L3321.step3_3_21d_of_F4 h5 h7 h9 h14
  have he := L3321.step3_3_21e_of_F4 h5 h14 hGA hd
  have hf := L3321.step3_3_21f_of_F4 h7 h9 h14 hGA he h15 hC34 h12 h20 hd hfQ
  have hgExt := L3321.step3_3_21gExt_of_F4 h9 h13 h14 hGA hd
  rcases hmod with ⟨Z, hZ, hZ2, -, hext⟩ | hsum
  · have hext' : Mod3321Ext T L := ⟨Z, hZ, hZ2, hext⟩
    exact hf G T M L D h ⟨e⟩ ⟨hab, Or.inl hext'⟩ (hgExt G T M L D h ⟨e⟩ hab hext')
  · exact hf G T M L D h ⟨e⟩ ⟨hab, Or.inr hsum⟩
      (L3321.step3_3_21gSum_of_F4 h5 h7 h13 h14 hGA he hC34 G T M L D h ⟨e⟩ hab hsum)

end CFSG.Quasithin.H13
