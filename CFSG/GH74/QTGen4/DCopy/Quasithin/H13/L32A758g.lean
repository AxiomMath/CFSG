module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A755f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A758f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC48b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

theorem L32A.thm14_7_53_of_F4
    (h38 : Lemma14_7_38_F4) (h30 : Lemma14_7_30_F4) (h48 : Lemma14_7_48_F4) (h52 : Thm14_7_52_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h13314 : A6.Stmt13_3_14_F4) : Thm14_7_53_F4 := by
  intro G _ _ T L V H S K hK hU3
  obtain ⟨rfl, C⟩ := L32A.ctx753_of_F4 h30 h48 h52 S hK hU3
  have := C.fact_tilde
  obtain ⟨e, E⟩ := C.exists_coord_F4 h38
  obtain ⟨γ, γ', g, k, N⟩ := C.exists_not1471_F4 h38
  have hVL := L32A.C.le_commutator_l1_F4 h1222 h1332 h1334 C.hyp
  obtain ⟨V₂, hV₂⟩ := C.hyp.exists_V2_F4 (stmt13_3_2_two_of_F4 h1332)
    (stmtL32NModule_of_inputs_F4 h1332 h1334) h1222
  exact C.false_of_data_F4 E L32A.M755.g2Facts h38 h1332 h1334 hVL hV₂ h13314 h1222 N

end CFSG.Quasithin.H13
