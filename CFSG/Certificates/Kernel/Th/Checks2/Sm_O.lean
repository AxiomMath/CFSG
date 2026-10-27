module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

theorem CFSG.KD.ThS.ob : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThS.RBf
    (nat_lit 2)) CFSG.KD.ThS.Bi) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThS.o13 : CFSG.KC.Th.BigS.primeOrder CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThS.RBf (nat_lit
    1)) (CFSG.KD.ThS.RBf (nat_lit 2)) CFSG.KD.ThS.Bi (nat_lit 294344331554) (nat_lit 21)) (nat_lit
    13) (nat_lit 5) = true := by
  quickRfl

theorem CFSG.KD.ThS.o31 : CFSG.KC.Th.BigS.primeOrder CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThS.RBf (nat_lit
    1)) (CFSG.KD.ThS.RBf (nat_lit 2)) CFSG.KD.ThS.Bi (nat_lit 149845545878689) (nat_lit 25))
    (nat_lit 31) (nat_lit 5) = true := by
  quickRfl

theorem CFSG.KD.ThS.o19 : CFSG.KC.Th.BigS.primeOrder CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThS.RBf (nat_lit 1)) (CFSG.KD.ThS.RBf
    (nat_lit 2))) (nat_lit 19) (nat_lit 5) = true := by
  quickRfl

theorem CFSG.KD.ThS.o2 : CFSG.KC.Th.BigS.primeOrder CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThS.RBf (nat_lit 1)) (nat_lit 2) (nat_lit 2) = true := by
  quickRfl

theorem CFSG.KD.ThS.lcm : Nat.beq (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN
    (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (nat_lit 1) (Nat.pow
    (nat_lit 2) CFSG.KD.ThS.n2)) (Nat.pow (nat_lit 3) CFSG.KD.ThS.n3)) (Nat.pow (nat_lit 5)
    CFSG.KD.ThS.n5)) (Nat.pow (nat_lit 7) CFSG.KD.ThS.n7)) (nat_lit 13)) (nat_lit 19)) (nat_lit 31))
    (Nat.mul (Nat.mul CFSG.KD.ThK1.nLive CFSG.KD.ThK3.nLive) CFSG.KD.ThB.SUM) = true := by
  quickRfl

theorem CFSG.KD.ThS.prim : CFSG.KC.Th.primOK (CFSG.KC.Th.BigS.sizesOf CFSG.KD.ThB.MD (Nat.mul
    CFSG.KD.ThK1.nLive CFSG.KD.ThK3.nLive) (nat_lit 10)) (nat_lit 10) CFSG.KD.ThB.SUM = true := by
  quickRfl

theorem CFSG.KD.ThS.prim19 : CFSG.KC.Th.andB (Nat.beq (Nat.mod (Nat.mul (Nat.mul CFSG.KD.ThK1.nLive
    CFSG.KD.ThK3.nLive) CFSG.KD.ThB.SUM) (nat_lit 19)) (nat_lit 0)) (CFSG.KC.Th.chkNe (Nat.mod
    (Nat.mul CFSG.KD.ThK1.nLive CFSG.KD.ThK3.nLive) (nat_lit 19)) (nat_lit 0)) = true := by
  quickRfl

theorem CFSG.KD.ThS.primND : Nat.beq CFSG.KD.ThB.ND (nat_lit 11) = true := by
  quickRfl

end
