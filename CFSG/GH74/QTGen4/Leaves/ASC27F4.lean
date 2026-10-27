module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27Holds
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27Assemble

public section

namespace CFSG.GH74.QTGen4.Leaves.ASC27

open CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Open CFSG.QuasithinUnique

theorem asc27Statement_F4_holds
    (hC132 : ASInputs.AS_C_1_32_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G :=
  asc27Statement_of_residue_of_inputs_F4 (fun G _ _ => H13.VolI.asc129Statement_holds G)
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    asA21SQTKSection asA36NoOddCover_holds B5.asB51_holds
    (fun G _ _ => asc27Residue_of_c132_F4 hC132 G)

end CFSG.GH74.QTGen4.Leaves.ASC27

end
