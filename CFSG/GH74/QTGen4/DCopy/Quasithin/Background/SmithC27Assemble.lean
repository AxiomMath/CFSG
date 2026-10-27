module

public import CFSG.Quasithin.Background.SmithC27Assemble
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem asc27Statement_of_residue_of_inputs_F4
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover) (hB51 : AsB51)
    (hres : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], SmithC27.ASC27Residue_F4 G) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G := fun G _ _ =>
  SmithC27.asc27Statement_of_residue_of_cases_F4 (hres G) fun _ _ _ _ h hc =>
    SmithC27.c27Concl_of_cases (hC129 G) hI hA21 hA36 hB51 h hc

end CFSG.Quasithin
