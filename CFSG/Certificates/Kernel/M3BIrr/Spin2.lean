module

public import CFSG.Certificates.Kernel.M3BIrr.Mats

public section

namespace CFSG.KD.M3BI

theorem spin2_0 : spinAt A0 B0 2 0 = true := by decide +kernel
theorem spin2_1 : spinAt A0 B0 2 1 = true := by decide +kernel
theorem spin2_2 : spinAt A0 B0 2 2 = true := by decide +kernel

end CFSG.KD.M3BI

end
