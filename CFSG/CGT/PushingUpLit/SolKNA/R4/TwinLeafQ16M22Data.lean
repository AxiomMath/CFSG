module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Check

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check

open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (Q16Data)

@[expose] def m22Q16 : Q16Data where
  n := 24
  pg := #[#[1, 0, 15, 12, 21, 5, 22, 7, 18, 9, 19, 11, 3, 14, 13, 2, 16, 17, 8, 10, 20, 4, 6, 23],
    #[0, 1, 18, 3, 5, 21, 14, 9, 15, 7, 23, 10, 12, 22, 8, 6, 4, 20, 13, 11, 17, 16, 2, 19],
    #[0, 1, 3, 8, 16, 21, 7, 13, 12, 6, 22, 18, 2, 9, 10, 11, 4, 17, 23, 14, 20, 5, 19, 15],
    #[1, 0, 3, 18, 21, 5, 9, 14, 12, 22, 8, 6, 15, 7, 23, 10, 16, 17, 19, 2, 20, 4, 11, 13]]
  qW := #[[0], [1], [2], [3]]
  qKeys := [0, 1, 2, 3, 4, 5, 8, 9]
  qFuel := 257
  qOrd := 256

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check
