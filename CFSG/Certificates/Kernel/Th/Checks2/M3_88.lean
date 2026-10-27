module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

theorem CFSG.KD.ThM3.fFQ : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (nat_lit 550)) (CFSG.KD.ThM3.RB (nat_lit 17))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThSeed.SA (CFSG.KD.ThM3.RB (nat_lit 550))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.fFX : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (nat_lit 553)) (CFSG.KD.ThM3.RB (nat_lit 13))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThSeed.SA (CFSG.KD.ThM3.RB (nat_lit 553))) = true := by
  quickRfl

end
