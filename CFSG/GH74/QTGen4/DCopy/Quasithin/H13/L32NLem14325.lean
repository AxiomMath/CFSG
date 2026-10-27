module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325o

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem lemma14325One_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1352 : A6.Stmt13_5_2_F4) (h1381 : Stmt13_8_1_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4) (h14324 : Lemma14324One_F4)
    (h64 : G64.LemmaG64) (hO : KGCert.KGSp6Order12096) : Lemma14325One_F4 := by
  intro G _ _ T L V h
  by_contra hne
  obtain ⟨V₂, g, D, C⟩ :=
    L14325.exists_ctx14325_F4 h1332 h1334 h1222 h12213 h37 h38 h39 h12813 h hne
  rcases h14324 G T L V h C.lt V₂ g C.plane C.gP C.gN D with h6 | ⟨hd, hi | hii | hiii⟩
  · exact C.not_g22_F4 hO h1332 h1352 h1381 h36 h39 h6
  · exact C.not_case_i_F4 h64 h1332 h1334 h1222 h12213 h12810 hd hi
  · exact C.not_case_ii_F4 h12810 hd hii
  · exact C.not_case_iii_F4 h1332 h1352 h1381 h36 h39 hd hiii

end CFSG.Quasithin.H13
