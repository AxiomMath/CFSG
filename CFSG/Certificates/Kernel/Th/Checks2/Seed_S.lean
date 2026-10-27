module

public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

theorem CFSG.KD.ThSeed.dA : CFSG.KC.Th.SeedS.decOK CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.LA = true := by
  quickRfl

theorem CFSG.KD.ThSeed.dB : CFSG.KC.Th.SeedS.decOK CFSG.KD.ThSeed.SB CFSG.KD.ThSeed.LB = true := by
  quickRfl

theorem CFSG.KD.ThSeed.pF : CFSG.KC.Th.SeedS.packOK CFSG.KD.ThSeed.SF CFSG.KC.Th.SeedS.fcRowsList =
    true := by
  quickRfl

theorem CFSG.KD.ThSeed.aa : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThSeed.SA
    CFSG.KD.ThSeed.SA) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThSeed.bbb : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThSeed.SB CFSG.KD.ThSeed.SB) CFSG.KD.ThSeed.SB)
    CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThSeed.aF : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.trB CFSG.KD.ThS.tm0 CFSG.KD.ThS.tm1 CFSG.KD.ThS.tm2
    CFSG.KD.ThS.tm3 CFSG.KD.ThS.tm4 CFSG.KD.ThS.tm5 CFSG.KD.ThS.tm6 CFSG.KD.ThS.tm7
    CFSG.KD.ThSeed.SA) CFSG.KD.ThSeed.SF) CFSG.KD.ThSeed.SA) CFSG.KD.ThSeed.SF = true := by
  quickRfl

theorem CFSG.KD.ThSeed.bF : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.trB CFSG.KD.ThS.tm0 CFSG.KD.ThS.tm1 CFSG.KD.ThS.tm2
    CFSG.KD.ThS.tm3 CFSG.KD.ThS.tm4 CFSG.KD.ThS.tm5 CFSG.KD.ThS.tm6 CFSG.KD.ThS.tm7
    CFSG.KD.ThSeed.SB) CFSG.KD.ThSeed.SF) CFSG.KD.ThSeed.SB) CFSG.KD.ThSeed.SF = true := by
  quickRfl

end
