module

public import CFSG.Certificates.Kernel.M3BIrr.Mats

public section

namespace CFSG.KD.M3BI

theorem spin0_0 : spinAt A0 B0 0 0 = true := by decide +kernel
theorem spin0_1 : spinAt A0 B0 0 1 = true := by decide +kernel
theorem spin0_2 : spinAt A0 B0 0 2 = true := by decide +kernel

end CFSG.KD.M3BI

end
