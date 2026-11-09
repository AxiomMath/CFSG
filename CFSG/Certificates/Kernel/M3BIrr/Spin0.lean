module

public import CFSG.Certificates.Kernel.M3BIrr.SpinRow

public section

namespace CFSG.KD.M3BI

theorem spin0_0 : spinAt A0 B0 0 0 = true := by decide +kernel
theorem spin0_1_r0 : spinRow A0 B0 0 1 0 = true := by decide +kernel
theorem spin0_1_r1 : spinRow A0 B0 0 1 1 = true := by decide +kernel
theorem spin0_1_r2 : spinRow A0 B0 0 1 2 = true := by decide +kernel
theorem spin0_1 : spinAt A0 B0 0 1 = true :=
  spinAt_of_rows spin0_1_r0 spin0_1_r1 spin0_1_r2
theorem spin0_2_r0 : spinRow A0 B0 0 2 0 = true := by decide +kernel
theorem spin0_2_r1 : spinRow A0 B0 0 2 1 = true := by decide +kernel
theorem spin0_2_r2 : spinRow A0 B0 0 2 2 = true := by decide +kernel
theorem spin0_2 : spinAt A0 B0 0 2 = true :=
  spinAt_of_rows spin0_2_r0 spin0_2_r1 spin0_2_r2

end CFSG.KD.M3BI

end
