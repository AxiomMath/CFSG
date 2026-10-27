module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1525
public import CFSG.Quasithin.H13.A5Quad
public import CFSG.Quasithin.H13.A5RowsOut

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem input13518_of_facts_F4
    (h1323 : Input1323Two_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hF956 : StmtF956i) (h38 : A38ForSQTK) (hF : Facts1321) (hA7 : FactA7Grp1321)
    (hL3 : FactL3Grp1321) : Input13518_F4 :=
  input13518_of_F4 h1323 h1326 h1336 hF956 h38 hF factRankRows1321 hA7 hL3 factOutRows1321
    factQuadRows1321

end CFSG.Quasithin.H13.A5
