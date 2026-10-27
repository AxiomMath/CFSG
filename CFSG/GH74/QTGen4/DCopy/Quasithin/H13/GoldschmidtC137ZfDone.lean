module

public import CFSG.Quasithin.H13.GoldschmidtC137SQFinal
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137ZfFinal

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin

section Complete

theorem c137StatementFiveZ_complete_F4
    (hE22 : E2.E22StatementNoN) (hC132 : ASInputs.AS_C_1_32_F4)
    (hC134 : C134L32Corr_F4) : C137StatementFiveZ_F4 :=
  c137StatementFiveZ_final_F4 hE22 hC132 hC134 c137SQTKSupply_holds

end Complete

end CFSG.Quasithin.H13.U3.GC137
