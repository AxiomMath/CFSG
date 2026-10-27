module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16L32
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem16

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

open Orbit

open Lem16L32

theorem stmt12_2_16_of_sylowFix_F4 (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4) (hL52 : OrbitL52Ten)
    (hsyl : L32FourSylowFix) (hHat : OrbitHatA6Six) (hG2c : G2NaturalCover)
    (h6 : CoreSixTwoCentral) (hW : G2WeylTwoCentral) (h8 : Lem12216CoreEight_F4) :
    Stmt12_2_16_F4 :=
  stmt12_2_16_of_F4 h1222 h331 hL52 (orbitL32Four_of hsyl) hHat hG2c h6 hW h8

end CFSG.Quasithin.H13
