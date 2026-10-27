module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma3K1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma3
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139Holds
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3SL3
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3L249

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13

theorem lemma12_9_3K1_F4_of_closed
    (h1222 : Stmt12_2_2_F4) : Lemma12_9_3K1_F4 :=
  lemma12_9_3K1_of_inputs_F4 h1222 VolI.a36ForSQTK_holds CFSG.Quasithin.a37ForSQTK_proved
    CFSG.Quasithin.a38ForSQTK_proved CFSG.Quasithin.a39ForSQTK_proved a312ForSQTK_proved
    (dynkinFact1293_of dynkinFact1293SL3_holds)

theorem lemma12_9_3One_F4_of_closed
    (h1222 : Stmt12_2_2_F4) : Lemma12_9_3One_F4 :=
  lemma12_9_3_one_F4 h1222 CFSG.Quasithin.a37ForSQTK_proved CFSG.Quasithin.a38ForSQTK_proved
    CFSG.Quasithin.a39ForSQTK_proved

end CFSG.GH74.QTGen4.Leaves
