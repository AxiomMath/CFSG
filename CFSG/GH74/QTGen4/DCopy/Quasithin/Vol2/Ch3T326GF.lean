module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11SecOE1E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T326GE
public import CFSG.Quasithin.Background.F918YM
public import CFSG.Quasithin.Background.SmithD321Holds
public import CFSG.Quasithin.Vol2.Ch10SecC3A
public import CFSG.Quasithin.Vol2.Ch11SecOE1C
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ9
public import CFSG.Quasithin.Vol2.Ch3T326PL
public import CFSG.Quasithin.Vol2.GoldschmidtC58Proved
public import CFSG.Quasithin.Vol2.GoldschmidtTD317
public import CFSG.Quasithin.Vol2.GoldschmidtTD32
public import CFSG.Quasithin.Vol2.GoldschmidtTDTmpL6

public section
namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt3_2_6C_of_stmt331_F4
    (h331 : Stmt3_3_1_F4) : Stmt3_2_6C_F4 :=
  have h3228 := Vol2.Ch10.tmpL6_3_2_2_eight_proved
  have h3222 := Vol2.Ch10.tmpL6_3_2_2_two_of h3228 stmt3_2_3_proved
  have hL38 : D3L38 := d3L38_of_a38 d3A38_holds
  have h9 := SmithD321.a38B42_of Vol2.Ch10.SecA.facts10_1_holds insp5aNonShape_holds
  stmt3_2_6C_of_inputs'_F4 h331 h3222 h3228 Ch3T316W.theorem316Statement_holds
    Vol2Native.a37ForSQTKCat_proved C129Native.a38ForSQTKCat_proved d37_holds
    SmithD39Two.d36c_holds hL38
    (d36B48q_of_narrow SmithD39Two.d36c_holds (d36B48qN_proved H13.d35_proved d36A38_holds hL38))
    (Vol2.Ch11.tmpL6_3_2_2_six_of_F4 theoremC58_proved as317Sylow_proved h331 h3228
      (Vol2.Ch11.tmpL6_3_2_2_four_of h3222))
    d321_holds
    (d321O2_of asA21SQTKSection asB42_holds h9 SmithD39Two.d36c_holds d37_holds asB56_holds
      SmithD39Two.d38Top_holds a23SQTKListFact H13.simpleThreePrimeSuzukiFact hL38)
    asA21SQTKSection asB42_holds h9 asB56_holds SmithD39Two.d38Top_holds a23SQTKListFact
    H13.simpleThreePrimeSuzukiFact

end CFSG.Quasithin.H13.T326
