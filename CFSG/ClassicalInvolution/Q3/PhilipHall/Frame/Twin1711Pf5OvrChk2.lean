module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrData

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open PkG

theorem recs2_true : recsChk OMs2 ovrRecs2 = true := by decide +kernel

theorem clos2_true : omClosedSlice OMs2 = true := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
