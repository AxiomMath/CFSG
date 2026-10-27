module

public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137L32Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137U33Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137ZfCase

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin

theorem c137StatementFiveSQTKZ_final_F4
    (hE22 : E2.E22StatementNoN) (hC132 : ASInputs.AS_C_1_32_F4)
    (hC134 : C134L32Corr_F4) : C137StatementFiveSQTKZ_F4 :=
  c137StatementFiveSQTKZ_of_cases_F4 (fun G _ _ => C124.c124StatementSQTK_of_e22 hE22 G)
    (c137CaseL32_final_F4 hC134) (c137CaseU33_final_F4 hC132)
    (c137CaseS6Z_of_F4 (fun G _ _ => C124.c124StatementSQTK_of_e22 hE22 G) hC132)

theorem c137StatementFiveZ_final_F4
    (hE22 : E2.E22StatementNoN) (hC132 : ASInputs.AS_C_1_32_F4)
    (hC134 : C134L32Corr_F4) (hs : C137SQTKSupply) : C137StatementFiveZ_F4 :=
  c137StatementFiveZ_of_sqtk_F4 (c137StatementFiveSQTKZ_final_F4 hE22 hC132 hC134) hs

end CFSG.Quasithin.H13.U3.GC137
