module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltMult
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55D4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L5
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MTwo
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55McLyCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1Asm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Ree
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Sl2Five
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Sp4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55U3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55U4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55U5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem parts55_leaves (hCross : Cross55) (hSpor : Cell55 FSpor) : Parts55 where
  cross := hCross
  sl2five := sl2Five55
  alt := cell55_of_n1 multAlt55 n1fam_alt
  spor := hSpor
  mcly := cell55_of_n1 multAlt55 n1fam_mcly
  two := cell55_of_n1 multAlt55 n1fam_two
  l2 := def55_l2
  l3 := def55_l3
  u3 := def55_u3
  sp4 := def55_sp4
  g2 := def55_g2
  d4 := def55_d4
  l4 := def55_l4
  u4 := def55_u4
  ree := def55_ree
  l5 := excl55_fl5
  u5 := excl55_fu5

theorem cells55_leaves (hCross : Cross55) (hSpor : Cell55 FSpor) : Cells55 :=
  cells55_of_parts (parts55_leaves hCross hSpor)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
