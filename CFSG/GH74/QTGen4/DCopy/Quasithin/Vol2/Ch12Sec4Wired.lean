module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Lemma7
public import CFSG.Quasithin.H13.VolIAltCoverG2
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Norm
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Fix

public section

namespace CFSG.Quasithin.H13

theorem pre1242_of_stmts_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) : Pre1242_F4 :=
  pre1242_of_F4 h331 h1222 VolI.g2NaturalCover_holds l52TenSylowFixedLine

theorem lemma12_4_7_of_stmts_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4) (h1246 : Lemma12_4_6_F4) :
    Lemma12_4_7_F4 :=
  lemma12_4_7_of_F4 h331 h1222 hpre h1246 VolI.g2NaturalCover_holds Orbit.orbitG2Weyl
    Orbit.g2WeylNormalizerOrbits

end CFSG.Quasithin.H13
