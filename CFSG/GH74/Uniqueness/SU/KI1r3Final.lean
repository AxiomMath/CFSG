module

public import CFSG.GH74.Uniqueness.SU.KI1r3Fam
public import CFSG.GH74.Uniqueness.SU.KI1r3FamL2
public import CFSG.GH74.Uniqueness.SU.KI1r3FamBender
public import CFSG.GH74.Uniqueness.SU.KI1r3FamLie
public import CFSG.GH74.Uniqueness.SU.KI1r3FamSp1
public import CFSG.GH74.Uniqueness.SU.KI1r3FamSp2

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

theorem famFacts
    : FamFacts where
  l2 := famL2
  alt := famAlt
  m11 := famSp_M11
  m12 := famSp_M12
  m22 := famSp_M22
  m23 := famSp_M23
  j1 := famSp_J1
  j2 := famSp_J2
  j3 := famSp_J3
  mcl := famSp_McL
  ly := famSp_Ly
  psl3 := famLie_psl3
  psl4 := famLie_psl4
  psl5 := famLie_psl5
  psu3 := famLie_psu3
  psu4 := famLie_psu4
  psu5 := famLie_psu5
  psp2 := famLie_psp2
  g2 := famLie_g2
  d4 := famLie_3d4
  ree := famRee
  bender := famBender

theorem ki1r3
    : KI1r3 := ki1r3_of_F61 (f61r3_of_famFacts famFacts)

end CFSG.GH74.Uniqueness.SU.K.R3
