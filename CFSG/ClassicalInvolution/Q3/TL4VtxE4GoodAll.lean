module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4GoodSp6
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4GoodO8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem e4QuatNoGood_of_exLie
    {M : Type} [Group M] [Finite M]
    (hM : PhilipHall.QuaternionBridge.ExLie M) : E4QuatNoGood M :=
  hM.elim E4Sp6.e4QuatNoGood_PSp E4O8.e4QuatNoGood_POmegaPlus

end CFSG.ClassicalInvolution.Q3.TL4
