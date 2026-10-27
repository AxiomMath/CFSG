module

public section

namespace CFSG.KC.SchurC

@[expose] def m24a2 : List (Nat × Bool) := [(0, true), (0, true)]
@[expose] def m24b3 : List (Nat × Bool) := [(1, true), (1, true), (1, true)]
@[expose] def m24ab23 : List (Nat × Bool) := [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)]
@[expose] def m24r4 : List (Nat × Bool) := [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)]
@[expose] def m24r5 : List (Nat × Bool) := [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true)]
@[expose] def m24r6 : List (Nat × Bool) := [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)]
@[expose] def m24r7 : List (Nat × Bool) := [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]

@[expose] def tz (b : Bool) (w : List (Nat × Bool)) : List (Nat × Bool) := cond b (w ++ [(2, true)]) w

@[expose] def crels (c0 c1 c2 c3 c4 : Bool) : List (List (Nat × Bool)) :=
  [[(2, true), (2, true)], [(2, true), (0, true), (2, false), (0, false)],
    [(2, true), (1, true), (2, false), (1, false)], tz c0 m24a2, m24b3, m24ab23, tz c1 m24r4,
    tz c2 m24r5, tz c3 m24r6, tz c4 m24r7]

end CFSG.KC.SchurC

end
