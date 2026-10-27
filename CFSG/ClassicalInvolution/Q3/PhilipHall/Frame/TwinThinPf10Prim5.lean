module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

@[expose] def chains5 : List (List (Step 5)) :=
  [
    [(0, 1, [(1, 2), (3, 4)]), (0, 2, [(2, 3), (3, 4)]), (0, 3, [(2, 3), (3, 4)])],
    [(0, 2, [(2, 3), (3, 4)]), (0, 3, [(2, 3), (3, 4)]), (0, 2, [(1, 2), (3, 4)])],
    [(0, 3, [(2, 3), (3, 4)]), (0, 4, [(2, 3), (3, 4)]), (0, 2, [(1, 2), (3, 4)])],
    [(0, 4, [(2, 3), (3, 4)]), (0, 2, [(2, 3), (3, 4)]), (0, 2, [(1, 2), (3, 4)])]
  ]


theorem fourSetPrim_five : FourSetPrim 5 :=
  fourSetPrim_of_check (chains := chains5) (by decide +kernel) (by decide +kernel)
    (a0 := {1, 2, 3, 4}) (by decide +kernel) (by decide +kernel)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
