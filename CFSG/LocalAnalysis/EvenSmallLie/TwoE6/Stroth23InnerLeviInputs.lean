module

public import CFSG.Monster.B.TwoA.Unitary.Form

public section

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open CFSG.Fischer

@[expose] def Ymat : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i =>
    CFSG.Monster.B.TwoA.Unitary.vec6 (#[1024, 2052, 16, 64, 1284, 3849][(i : ℕ)]!)

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
