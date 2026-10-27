module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137H6Case
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137ZfRed2
public import CFSG.Quasithin.H13.GoldschmidtC137KMod4

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem c137CaseS6Z_of_F4 (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4) : C137CaseS6Z_F4 :=
  c137CaseS6Z_of_M_F4
    (fun {_} _ _ _ L hU => ∃ k, (k = B3.Mod.ut0 ∨ k = B3.Mod.u0) ∧ Nonempty (KModel k (autI hU L)))
    (c137CaseS6M_of_F4 hC124 hC132) model_of_Z

end CFSG.Quasithin.H13.U3.GC137
