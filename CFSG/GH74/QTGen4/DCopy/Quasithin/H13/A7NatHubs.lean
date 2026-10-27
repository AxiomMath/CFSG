module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NatG10Owed
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.H13.VolIC129Holds

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin

theorem stmtA7NaturalModuleConfig_of_hubs_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1225 : Stmt12_2_5_F4) (h12212 : Stmt12_2_12_F4) (h12213 : Stmt12_2_13_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G)
    (h1229 : Stmt12_2_9_F4) (h3214 : Stmt3_2_14_F4)
    (hC41 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC41Statement G) (hF314 : A314Facts_F4)
    (hList : QuasithinUnique.Vol2Native.A312ListFactsCat) :
    StmtA7NaturalModuleConfig_F4 :=
  stmtA7NaturalModuleConfig_of_owed_F4 h1222 h331 h1225 h12212 h12213 hC27
    VolI.asc129Statement_holds hC111 hC19
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) h1229 h3214 hC41
    asB56_holds B5.asB51_holds hF314 hList

theorem stmt12_3_1_of_hubs_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1225 : Stmt12_2_5_F4) (h12212 : Stmt12_2_12_F4) (h12213 : Stmt12_2_13_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G)
    (h3214 : Stmt3_2_14_F4) (hC41 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC41Statement G)
    (hF314 : A314Facts_F4) (hList : QuasithinUnique.Vol2Native.A312ListFactsCat)
    (h1227 : Stmt12_2_7_F4) (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4) : Stmt12_3_1_F4 :=
  stmt12_3_1_of_owed_F4 h1222 h331 h1225 h12212 h12213 hC27 VolI.asc129Statement_holds hC111 hC19
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) h3214 hC41 asB56_holds
    B5.asB51_holds hF314 hList h1227 h1228 h1229

theorem stmtFiveA7Elim_of_hubs_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1225 : Stmt12_2_5_F4) (h12212 : Stmt12_2_12_F4) (h12213 : Stmt12_2_13_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G)
    (h3214 : Stmt3_2_14_F4) (hC41 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC41Statement G)
    (hF314 : A314Facts_F4) (hList : QuasithinUnique.Vol2Native.A312ListFactsCat)
    (h1227 : Stmt12_2_7_F4) (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4) : StmtFiveA7Elim_F4 :=
  stmtFiveA7Elim_of_inputs_F4
    (stmtA7NaturalModuleConfig_of_hubs_F4 h1222 h331 h1225 h12212 h12213 hC27 hC111 hC19 h1229
      h3214 hC41 hF314 hList)
    h12213 h1227 h1228 h1229 h331

end CFSG.Quasithin.H13.A7
