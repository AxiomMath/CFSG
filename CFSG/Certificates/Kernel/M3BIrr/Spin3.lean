module

public import CFSG.Certificates.Kernel.M3BIrr.SpinRow

public section

namespace CFSG.KD.M3BI

theorem spin3_0 : spinAt A0 B0 3 0 = true := by decide +kernel
theorem spin3_1_r0 : spinRow A0 B0 3 1 0 = true := by decide +kernel
theorem spin3_1_r1 : spinRow A0 B0 3 1 1 = true := by decide +kernel
theorem spin3_1_r2 : spinRow A0 B0 3 1 2 = true := by decide +kernel
theorem spin3_1 : spinAt A0 B0 3 1 = true :=
  spinAt_of_rows spin3_1_r0 spin3_1_r1 spin3_1_r2
theorem spin3_2_r0 : spinRow A0 B0 3 2 0 = true := by decide +kernel
theorem spin3_2_r1 : spinRow A0 B0 3 2 1 = true := by decide +kernel
theorem spin3_2_r2 : spinRow A0 B0 3 2 2 = true := by decide +kernel
theorem spin3_2 : spinAt A0 B0 3 2 = true :=
  spinAt_of_rows spin3_2_r0 spin3_2_r1 spin3_2_r2

end CFSG.KD.M3BI

end
