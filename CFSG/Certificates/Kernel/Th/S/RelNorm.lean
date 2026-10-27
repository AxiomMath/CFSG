module

public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.Data.DA_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.ThRelNorm

theorem norm_DA : CFSG.KC.relsNorm CFSG.KD.ThA.RR (nat_lit 29) = true := by quickRfl
theorem norm_DB : CFSG.KC.relsNorm CFSG.KD.ThB.RR (nat_lit 39) = true := by quickRfl

end CFSG.KD.ThRelNorm

end
