module

public import Certificates.Data.CFSGNative.F4.Basic

public section

namespace CFSG.Fischer

set_option maxHeartbeats 0 in
theorem countC_0 : CFSG.F4.Native.countC 0 = 2016 := by decide +kernel

set_option maxHeartbeats 0 in
theorem countC_1 : CFSG.F4.Native.countC 1 = 528 := by decide +kernel

set_option maxHeartbeats 0 in
theorem countC_2 : CFSG.F4.Native.countC 2 = 120 := by decide +kernel

set_option maxHeartbeats 0 in
theorem countC_3 : CFSG.F4.Native.countC 3 = 36 := by decide +kernel

set_option maxHeartbeats 0 in
theorem countC_4 : CFSG.F4.Native.countC 4 = 6 := by decide +kernel

set_option maxHeartbeats 0 in
theorem countC_5 : CFSG.F4.Native.countC 5 = 3 := by decide +kernel

end CFSG.Fischer
