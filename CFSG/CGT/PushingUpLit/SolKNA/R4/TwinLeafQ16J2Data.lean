module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Check

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check

open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (Q16Data)

@[expose] def j2Q16 : Q16Data where
  n := 315
  pg := CFSG.ComponentClassification.J2Cover.sylowStrong.extract 0 3
  qW := #[[0], [1], [2]]
  qKeys := [1, 3]
  qFuel := 257
  qOrd := 256

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check
