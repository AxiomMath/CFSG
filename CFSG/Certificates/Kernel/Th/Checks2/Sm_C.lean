module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

theorem CFSG.KD.ThS.k0 : CFSG.KC.Th.BigS.constsOK CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.tm0
    CFSG.KD.ThS.tm1 CFSG.KD.ThS.tm2 CFSG.KD.ThS.tm3 CFSG.KD.ThS.tm4 CFSG.KD.ThS.tm5 CFSG.KD.ThS.tm6
    CFSG.KD.ThS.tm7 CFSG.KD.ThS.up CFSG.KD.ThS.dg CFSG.KD.ThS.ONE = true := by
  quickRfl

end
