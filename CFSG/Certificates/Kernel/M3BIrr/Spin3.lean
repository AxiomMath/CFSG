module

public import CFSG.Certificates.Kernel.M3BIrr.Mats

public section

namespace CFSG.KD.M3BI

theorem spin3_0 : spinAt A0 B0 3 0 = true := by decide +kernel
theorem spin3_1 : spinAt A0 B0 3 1 = true := by decide +kernel
theorem spin3_2 : spinAt A0 B0 3 2 = true := by decide +kernel

end CFSG.KD.M3BI

end
