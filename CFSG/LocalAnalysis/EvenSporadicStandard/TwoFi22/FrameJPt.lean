module

public import CFSG.Sporadic.Fi23.Class

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.Sporadic.Fi23

@[expose] def fjIdx : List ℕ :=
  [0, 830, 1493, 1795, 10795, 4391, 13637, 29382, 17196, 14554, 8136, 4576, 21555, 13389, 6282,
    22056, 29944, 29779, 17072, 15480, 28185, 18757, 14065]

@[expose] noncomputable def fjPt (i : Fin 23) : J :=
  conjPt (fjIdx.getD i.val 0)

end CFSG.EvenSporadicStandard.TwoFi22.FrameJ

end
