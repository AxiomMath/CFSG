module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1233
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1236Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238Main

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin

theorem stmtA7NaturalModuleConfig_of_inputs_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1225 : Stmt12_2_5_F4) (h12212 : Stmt12_2_12_F4) (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hF : A318Facts)
    (hI16 : AsI16AltSevenCover) (hfour : A7FourExcluded_F4) (hI1 : Insp1236) (hI2 : InspSL2NoA6)
    (hgap : Gap1237KeJ_F4) (hNQ : Insp1238NonQ_F4) (hIQ : Insp1238Q_F4) (hIY : Insp1238Y) :
    StmtA7NaturalModuleConfig_F4 := by
  have h1236 := stmt12_3_6_of_inputs_F4 h1222 h331 h12212 h1225 h39 hC27 hC129 hF hI1 hI2
  exact stmtA7NaturalModuleConfig_of_lemmas_F4 h1222 h331 (stmt12_3_3_of_four_F4 h1222 hI16 hfour)
    h1236 (stmt12_3_8_of_inputs_F4 h1222 h331 h1225 h1236 h39 hgap hNQ hIQ hIY)

theorem stmt12_3_1_of_named_inputs_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1225 : Stmt12_2_5_F4) (h12212 : Stmt12_2_12_F4) (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hF : A318Facts)
    (hI16 : AsI16AltSevenCover) (hfour : A7FourExcluded_F4) (hI1 : Insp1236) (hI2 : InspSL2NoA6)
    (hgap : Gap1237KeJ_F4) (hNQ : Insp1238NonQ_F4) (hIQ : Insp1238Q_F4) (hIY : Insp1238Y)
    (h12213 : Stmt12_2_13_F4) (h1227 : Stmt12_2_7_F4) (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4) :
    Stmt12_3_1_F4 := by
  have h1236 := stmt12_3_6_of_inputs_F4 h1222 h331 h12212 h1225 h39 hC27 hC129 hF hI1 hI2
  exact stmt12_3_1_of_lemmas_F4 h1222 h331 (stmt12_3_3_of_four_F4 h1222 hI16 hfour) h1236
    (stmt12_3_8_of_inputs_F4 h1222 h331 h1225 h1236 h39 hgap hNQ hIQ hIY) h12213 h1227 h1228 h1229

end CFSG.Quasithin.H13.A7
