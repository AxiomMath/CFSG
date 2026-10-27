module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Of4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76V
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76X
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Z2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

theorem lem1376L1KSmallOdd_of_L32_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hL : Lem1376OddNCL32_F4) : Lem1376L1KSmallOdd_F4 :=
  lem1376L1KSmallOdd_of_F4 (lem1376L1KSmallOddComm_of_F4 h139 h37 h38 h13315)
    (lem1376L1KSmallOddNC_of_F4 (lem1376OddNCA5_of_F4 h139 h37 h38 h13315)
      (lem1376OddNCBig_of_F4 h139 h37 h38 h13315 h1356two) hL)

theorem lem1376L1KSmall_of_L32_F4 (hF : A318Facts)
    (h36 : A36ForSQTK) (h139 : Stmt13_3_9_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (hL : Lem1376OddNCL32_F4) :
    Lem1376L1KSmall_F4 :=
  lem1376L1KSmall_of_F4 (lem1376L1KSmallEven_of_F4 hF h36 h38 h13315 h1356two)
    (lem1376L1KSmallOdd_of_L32_F4 h139 h37 h38 h13315 h1356two hL)

theorem lem1376Full_of_atoms_F4
    (hL : Lem1376OddNCL32_F4) (h3 : Lem1376NThree_F4) (h5 : Lem1376Five_F4) (hF : A318Facts)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h139 : Stmt13_3_9_F4)
    (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (h1337 : Stmt13_3_7_F4) : Lem1376Full_F4 :=
  lem1376Full_of_F4 (lem1376L1K_of_F4 (lem1376L1KSmall_of_L32_F4 hF h36 h139 h37 h38 h13315 h1356two hL)
    hF h36 h38 h13315 h1356two) h3 h5 h37 h38 h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
