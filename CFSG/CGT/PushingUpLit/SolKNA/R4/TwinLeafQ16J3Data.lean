module

public import CFSG.Sporadic.SmallOddCore.J3Data
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Check

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check

open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (Q16Data)

@[expose] def j3Q16 : Q16Data where
  n := 6156
  pg := (CFSG.Sporadic.SmallOddCore.j3SylowGenTbls.map
    CFSG.Sporadic.SmallOddCore.Native.natArr).toArray
  qW := #[[0], [1], [2], [3], [4], [5], [6], [7]]
  qKeys := [0, 1]
  qFuel := 257
  qOrd := 256

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check
