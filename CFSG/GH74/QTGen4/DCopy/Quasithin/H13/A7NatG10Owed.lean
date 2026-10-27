module

public import CFSG.Quasithin.H13.A7NatG10Owed
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1233Four
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1233Lin
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1237Gap
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238NQOwed
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238QTab
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238YQOwed

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin

theorem stmtA7NaturalModuleConfig_of_owed_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1225 : Stmt12_2_5_F4) (h12212 : Stmt12_2_12_F4) (h12213 : Stmt12_2_13_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G) (hF : A318Facts)
    (h1229 : Stmt12_2_9_F4) (h3214 : Stmt3_2_14_F4)
    (hC41 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC41Statement G) (h56 : AsB56)
    (h51 : AsB51) (hF314 : A314Facts_F4)
    (hList : QuasithinUnique.Vol2Native.A312ListFactsCat) :
    StmtA7NaturalModuleConfig_F4 :=
  have h39 := QuasithinUnique.Vol2Native.a39ForSQTKCat_proved
  have hInsK := insp1233K_of_F4 h1222 h1225 hC41 h3214 (Lin.insp1233KLin_of_F4 h1222 hC27 h51)
  have h1233 : Stmt12_3_3_F4 := stmt12_3_3_of_four_F4 h1222 asI16AltSevenCover_holds
    (a7FourExcluded_of_inputs_F4 h1222 h12213 h1225 h12212 h39 hC129 hC111 hC19
      (insp1233Mod_of_F4 h1222 h1225) hInsK)
  stmtA7NaturalModuleConfig_of_named_inputs_F4 h1222 h331 h1225 h12212 h12213 h39 hC27 hC129 hC111
    hC19 hF asI16AltSevenCover_holds (insp1233Mod_of_F4 h1222 h1225) hInsK insp1236_proved
    inspSL2NoA6_proved (gap1237KeJ_of_F4 h1222 h331 h1229) (insp1238NonQ_of_F4 h3214)
    (insp1238Q_of_F4 (insp1238QTab_of_F4 hF314 (a312ForSQTKCat_of_list h39 hList) h1222 h1225) h1222
      h331 h1233)
    (insp1238Y_of h56)

theorem stmt12_3_1_of_owed_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1225 : Stmt12_2_5_F4) (h12212 : Stmt12_2_12_F4) (h12213 : Stmt12_2_13_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G) (hF : A318Facts)
    (h3214 : Stmt3_2_14_F4) (hC41 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC41Statement G)
    (h56 : AsB56) (h51 : AsB51) (hF314 : A314Facts_F4)
    (hList : QuasithinUnique.Vol2Native.A312ListFactsCat)
    (h1227 : Stmt12_2_7_F4) (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4) : Stmt12_3_1_F4 :=
  have h39 := QuasithinUnique.Vol2Native.a39ForSQTKCat_proved
  have hfour := a7FourExcluded_of_inputs_F4 h1222 h12213 h1225 h12212 h39 hC129 hC111 hC19
    (insp1233Mod_of_F4 h1222 h1225)
    (insp1233K_of_F4 h1222 h1225 hC41 h3214 (Lin.insp1233KLin_of_F4 h1222 hC27 h51))
  have h1233 : Stmt12_3_3_F4 := stmt12_3_3_of_four_F4 h1222 asI16AltSevenCover_holds hfour
  stmt12_3_1_of_named_inputs_F4 h1222 h331 h1225 h12212 h39 hC27 hC129 hF asI16AltSevenCover_holds
    hfour insp1236_proved inspSL2NoA6_proved (gap1237KeJ_of_F4 h1222 h331 h1229)
    (insp1238NonQ_of_F4 h3214)
    (insp1238Q_of_F4 (insp1238QTab_of_F4 hF314 (a312ForSQTKCat_of_list h39 hList) h1222 h1225) h1222
      h331 h1233)
    (insp1238Y_of h56) h12213 h1227
    h1228 h1229

end CFSG.Quasithin.H13.A7
