module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrData

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open PkG

theorem recs0_true : recsChk OMs0 ovrRecs0 = true := by decide +kernel

theorem clos0_true : omClosedSlice OMs0 = true := by decide +kernel

theorem clos_head_true : omClosedSlice [GLO.getD 12 (one 256 240), GLO.getD 22 (one 256 240)] = true := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
