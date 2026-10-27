module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Check

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check

open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (Q16Data)

@[expose] def l34Q16 : Q16Data where
  n := 42
  pg := CFSG.PSL3Four.Native.gTabs
  qW := #[[5, 2, 5, 3, 4], [1, 5, 2, 5, 1], [2, 0, 0, 1, 5, 0, 1, 0, 0, 2, 0, 5, 2, 5, 1, 3, 3]]
  qKeys := [0, 3]
  qFuel := 257
  qOrd := 256

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check
