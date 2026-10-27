module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrData

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open PkG

theorem recs1_true : recsChk OMs1 ovrRecs1 = true := by decide +kernel

theorem clos1_true : omClosedSlice OMs1 = true := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
