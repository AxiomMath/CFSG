module

public import CFSG.Certificates.Kernel.M3BIrr.SpinRow

public section

namespace CFSG.KD.M3BI

theorem spin2_0 : spinAt A0 B0 2 0 = true := by decide +kernel
theorem spin2_1_r0 : spinRow A0 B0 2 1 0 = true := by decide +kernel
theorem spin2_1_r1 : spinRow A0 B0 2 1 1 = true := by decide +kernel
theorem spin2_1_r2 : spinRow A0 B0 2 1 2 = true := by decide +kernel
theorem spin2_1 : spinAt A0 B0 2 1 = true :=
  spinAt_of_rows spin2_1_r0 spin2_1_r1 spin2_1_r2
theorem spin2_2_r0 : spinRow A0 B0 2 2 0 = true := by decide +kernel
theorem spin2_2_r1 : spinRow A0 B0 2 2 1 = true := by decide +kernel
theorem spin2_2_r2 : spinRow A0 B0 2 2 2 = true := by decide +kernel
theorem spin2_2 : spinAt A0 B0 2 2 = true :=
  spinAt_of_rows spin2_2_r0 spin2_2_r1 spin2_2_r2

end CFSG.KD.M3BI

end
