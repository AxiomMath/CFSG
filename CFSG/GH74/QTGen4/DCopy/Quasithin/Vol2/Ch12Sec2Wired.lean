module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem10
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem16L32
public import CFSG.Quasithin.H13.VolIAltCoverG2
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitHatA6
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL32Four
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222
public import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6Six

public section

namespace CFSG.Quasithin.H13

theorem stmt12_2_10_of_1222_F4
    (h1222 : Stmt12_2_2_F4) : Stmt12_2_10_F4 :=
  stmt12_2_10_of_F4 h1222 out1222Fact_holds end1222Fact_holds

theorem stmt12_2_16_of_orbits_F4
    (h1222 : Stmt12_2_2_F4)
    (h331 : Stmt3_3_1_F4) (h6 : CoreSixTwoCentral) (hW : G2WeylTwoCentral)
    (h8 : Lem12216CoreEight_F4) : Stmt12_2_16_F4 :=
  stmt12_2_16_of_sylowFix_F4 h1222 h331 Orbit.orbitL52Ten Orbit.l32FourSylowFix
    (orbitHatA6Six_of Orbit.orbitTripleA6Six hatA6SixModel) VolI.g2NaturalCover_holds h6 hW h8

end CFSG.Quasithin.H13
