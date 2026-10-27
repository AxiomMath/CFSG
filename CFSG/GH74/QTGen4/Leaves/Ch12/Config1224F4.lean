module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem25D
public import CFSG.GH74.QTGen4.Leaves.Ch12.Lem25Gen4

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13

theorem stmt12_2_25_26_of_config_F4_of_inputs
    (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (h1216 : Stmt12_2_16_F4)
    (h1220 : Stmt12_2_20_F4) (hsplit : Lem12226Split_F4) : Stmt12_2_25_26_of_config_F4 :=
  stmt12_2_25_26_of_config_of_F4 h331 h1222 h323 h1216 h1220 lem12225YNormal_F4_holds
    (lem12225CTL3_F4_holds (lem12225Star_of_F4 h331 h1222 h323 h1216 h1220))
    lem12225N5_F4_holds hsplit

end CFSG.GH74.QTGen4.Leaves
