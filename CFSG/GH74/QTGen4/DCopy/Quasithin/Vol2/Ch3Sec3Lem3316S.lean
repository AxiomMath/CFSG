module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3316R
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.Quasithin.Vol2.Ch3Sec3Sp4Z
public import CFSG.Quasithin.Vol2.KGFact3312J1

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

theorem L3316.stmt3_3_16_of_inputs_F4
    (h6 : Stmt3_3_6) (h14 : Stmt3_3_14_F4) (hC32 : ASInputs.AS_C_1_32_F4) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) (h51 : AsB51) (h10 : Stmt3_3_10) (h12 : Step3_3_12RB_F4)
    (hGA : GriessAllModelsStatement) : Stmt3_3_16_F4 :=
  L3316.stmt3_3_16_of_steps_F4 h6 h14 hC32 factG2Cayley_holds h38 h39 h51 h10 h12
    KG3312.factJ1Norm3312_holds hGA L3316.factSp4BlockZ_holds

end CFSG.Quasithin.H13
