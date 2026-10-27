
module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.TsS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
public import CFSG.Certificates.Kernel.Th.S.Data.Ts_const
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

theorem CFSG.KD.ThTs.c0 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (nat_lit 4)) (CFSG.KD.ThTs.RB (nat_lit 28))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    (CFSG.KD.ThTs.RB (nat_lit 28)) (CFSG.KD.ThTs.RB (nat_lit 4))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.c1 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (nat_lit 5)) (CFSG.KD.ThTs.RB (nat_lit 28))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    (CFSG.KD.ThTs.RB (nat_lit 28)) (CFSG.KD.ThTs.RB (nat_lit 5))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.o0 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 15)) (CFSG.KD.ThTs.RB (nat_lit 18)))
    (CFSG.KD.ThTs.RB (nat_lit 14))) (CFSG.KD.ThTs.RB (nat_lit 4))) (CFSG.KD.ThTs.RB (nat_lit 14)))
    (CFSG.KD.ThTs.RB (nat_lit 25))) (CFSG.KD.ThTs.RB (nat_lit 15))) (CFSG.KD.ThTs.RB (nat_lit 17)))
    (CFSG.KD.ThTs.RB (nat_lit 14))) (CFSG.KD.ThTs.RB (nat_lit 17))) (CFSG.KD.ThTs.RB (nat_lit 14)))
    (CFSG.KD.ThTs.RB (nat_lit 16))) (CFSG.KD.ThTs.RB (nat_lit 14))) (CFSG.KD.ThTs.RB (nat_lit 16)))
    (CFSG.KD.ThTs.RB (nat_lit 18))) (CFSG.KD.ThTs.RB (nat_lit 1)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.o1 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (nat_lit 16)) (CFSG.KD.ThTs.RB (nat_lit 16))) (CFSG.KD.ThTs.RB (nat_lit 16))) (CFSG.KD.ThTs.RB
    (nat_lit 9))) (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 25))) (CFSG.KD.ThTs.RB
    (nat_lit 15))) (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 17))) (CFSG.KD.ThTs.RB
    (nat_lit 14))) (CFSG.KD.ThTs.RB (nat_lit 17))) (CFSG.KD.ThTs.RB (nat_lit 25))) (CFSG.KD.ThTs.RB
    (nat_lit 2)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.r : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 31)) (CFSG.KD.ThTs.RB (nat_lit 32)) =
    true := by
  quickRfl

theorem CFSG.KD.ThTs.r1 : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KD.ThTs.RB (nat_lit 31))
    CFSG.KD.ThS.ONE) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rz : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KD.ThTs.RB (nat_lit 31))
    (CFSG.KD.ThM3.RB (nat_lit 16))) = true := by
  quickRfl

end
