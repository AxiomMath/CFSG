module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrData

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open PkG

theorem recs3_true : recsChk OMs3 ovrRecs3 = true := by decide +kernel

theorem clos3_true : omClosedSlice OMs3 = true := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
