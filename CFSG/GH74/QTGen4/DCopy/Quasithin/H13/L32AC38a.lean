module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem hypF98_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (S : Setting147 G T L V H) :
    HypF98 T V L (fsuV1 T V) V H :=
  L1286.hypF98_of_abelian_F4 h1222 hA37 hA38 hA39
    (S.hyp.hyp1281One_F4 (stmt13_3_2_two_of_F4 h1332) (stmtL32NModule_of_inputs_F4 h1332 h1334))
    (S.hyp.isTSub_V1_F4 (stmtL32NModule_of_inputs_F4 h1332 h1334)) S.hyp.abelian S.hz

end CFSG.Quasithin.H13.L32A.C
