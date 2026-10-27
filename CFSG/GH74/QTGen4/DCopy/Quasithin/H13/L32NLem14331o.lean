module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems14331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm144Big

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem lemma14331CaseI_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4)
    (h14325 : Lemma14325One_F4) (h1434 : Lemma1434One_F4) (hF618 : F6.TheoremF618Cat)
    (hBig : A5.FactF618Big) (hL2 : A5.FactL2Three) : Lemma14331CaseI_F4 := by
  intro G _ _ T L V h hlt V₂ g hV₂ hgP hgN D hd hi
  obtain ⟨hc, z, b, l, C⟩ :=
    L14328.exists_ctx_of_F4 h1332 h1334 h1222 h12213 h12810 h hlt hV₂ hgP hgN
  by_contra hne
  obtain ⟨e, he, he1, he2⟩ := C.exists_e_F4 h14325 h1222 h12213 h12810 h12813 hne
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have h1283 := lemma12_8_3_F4 h12213
  have h1284 := lemma12_8_4_F4 h1222 h37 h38 h39
  have hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V) :=
    (h1284 G T L V 3 (h.hyp1281One_F4 h13322 hV) (fsuV1 T V) (l32nH T V) (h.isTSub_fsuV1_F4 hV)
      (h.isHzOne_l32nH_F4 h13322 hV h1283)).2.2.2
  have X : L14331.CaseI_F4 T L V g D e :=
    ⟨h14325, h1222, h12213, h12810, h12813, hQ, he, he1, he2, hi, hd⟩
  obtain ⟨hAm, hconc⟩ := C.caseI_f618_F4 D hF618 X
  have hAm' : IsGoldschmidtAmalgam (L14331.g2bar T L V l e) (L14331.g1bar T L V l e) :=
    { toIsGoldschmidtTriple := hAm.toIsGoldschmidtTriple.symm
      pCore_eq_bot := hAm.pCore_eq_bot }
  have hidx : CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup (L14331.dQ T L V l e))) → False := by
    intro hq
    obtain ⟨m, hm, h1, -⟩ := C.caseI_index_F4 D h1434 X hq hAm
    exact C.caseI_false_F4 D X (by rcases hm with rfl | rfl <;> omega)
  rcases hconc with h | h <;> rcases h with h1 | h2 | h3 | hrest
  · exact (C.caseI_not_caseOne_F4 D X).1 h1
  · exact C.caseI_not_caseTwo_F4 D X h2
  · exact C.caseI_not_caseThree_F4 D h1434 hL2 X h3
  · exact hidx (hBig _ _ _ hAm hrest).1
  · exact (C.caseI_not_caseOne_F4 D X).2 h1
  · exact C.caseI_not_caseTwo_F4 D X h2
  · exact C.caseI_not_caseThree_F4 D h1434 hL2 X h3
  · exact hidx (hBig _ _ _ hAm' hrest).1

end CFSG.Quasithin.H13
