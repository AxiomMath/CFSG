module

public import CFSG.GH74.AS16.E2.Skeleton
public import CFSG.GH74.AS16.E2.Residual

public section

namespace CFSG.GH74.AS16.E2

open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.Uniqueness (S_CorZD)

theorem s_alss3121E2_of
    (hCL : ComponentList) (hZD : S_CorZD) (hP : PumpUpData)
    (hD3 : K0Data3) : S_ALSS3121E2 :=
  s_alss3121E2_of_leaves hCL hP (e2Leaves hZD hCL hD3)

end CFSG.GH74.AS16.E2
