module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137U33Case
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.F918D9
public import CFSG.Quasithin.Background.FFCAssembly51
public import CFSG.Quasithin.Background.SmithA36
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.SmithB51Sp4
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Fin

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin


theorem c137CaseU33_final_F4
    (hC132 : ASInputs.AS_C_1_32_F4) : C137CaseU33_F4 :=
  c137CaseU33_of_F4
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    asA21SQTKSection asA36NoOddCover_holds H13.VolI.g2NaturalCover_holds
    H13.g2DerivedNormalizerZorn hC132 u33G2Facts_holds

end CFSG.Quasithin.H13.U3.GC137
