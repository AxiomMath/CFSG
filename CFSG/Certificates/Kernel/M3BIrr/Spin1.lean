module

public import CFSG.Certificates.Kernel.M3BIrr.Mats

public section

namespace CFSG.KD.M3BI

theorem spin1_0 : spinAt A0 B0 1 0 = true := by decide +kernel
theorem spin1_1 : spinAt A0 B0 1 1 = true := by decide +kernel
theorem spin1_2 : spinAt A0 B0 1 2 = true := by decide +kernel

end CFSG.KD.M3BI

end
