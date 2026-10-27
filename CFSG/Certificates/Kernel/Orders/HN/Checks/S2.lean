module

public import CFSG.Certificates.Kernel.Orders.BlockChecks
public import CFSG.Certificates.Kernel.Orders.HN.Checks.Tab
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHN

open CFSG.KC.Ord

local notation "MUL" =>
  mulR (nat_lit 5) (nat_lit 13) (nat_lit 0x6c1) (nat_lit 0x85) (nat_lit 9) L H CM RM

local notation "VEC" =>
  vecR (nat_lit 5) (nat_lit 13) (nat_lit 0x6c1) (nat_lit 0x85) (nat_lit 9) LV HV RM

theorem s2_pr : regsIn S2.PR (nat_lit 14) (nat_lit 799) = true := by quickRfl

theorem s2_bl : blocksOK S2.BL (nat_lit 7) (nat_lit 14) = true := by quickRfl

theorem s2_pw : pwOK RW MUL S2.PR S2.PW (nat_lit 14) (nat_lit 2) (nat_lit 799) = true := by quickRfl

theorem s2_pc : Nat.beq (runPc RW MUL ONE S2.PR S2.PW (nat_lit 14) 2 (nat_lit 1) S2.PC 1)
    (Nat.add 1 (nat_lit 14)) = true := by
  quickRfl

@[expose] noncomputable def PT2 (b : Nat) : Nat → Nat :=
  [PT2_0, PT2_1, PT2_2, PT2_3, PT2_4, PT2_5, PT2_6].getD b PT2_0

@[expose] def bf2 (b : Nat) : Bool :=
  blkBF RW VEC (validM (nat_lit 5) (nat_lit 0x6c1) LV HV) S2.PR S2.BL (nat_lit 14) PT2 b

@[expose] def bt2 (b : Nat) : Bool := blkBT RW VEC S2.PR S2.BL (nat_lit 14) PT2 S2.TC S2.N b

@[expose] def bs2 (b : Nat) : Bool := blkBS PT2 S2.N S2.SC S2.SS b

@[expose] def bn2 (b : Nat) : Bool := blkBN (nat_lit 2) S2.BL S2.N S2.SS b

end CFSG.KD.OrdHN

#kc_each CFSG.KD.OrdHN.bf2 0 7
#kc_each CFSG.KD.OrdHN.bt2 0 7
#kc_each CFSG.KD.OrdHN.bs2 0 7
#kc_each CFSG.KD.OrdHN.bn2 0 7

namespace CFSG.KD.OrdHN

#kc_forall_chunks S2.BF.all (fun b => bf2 b = true) 7 CFSG.KD.OrdHN.bf2 1
#kc_forall_chunks S2.BT.all (fun b => bt2 b = true) 7 CFSG.KD.OrdHN.bt2 1
#kc_forall_chunks S2.BS.all (fun b => bs2 b = true) 7 CFSG.KD.OrdHN.bs2 1
#kc_forall_chunks S2.BN.all (fun b => bn2 b = true) 7 CFSG.KD.OrdHN.bn2 1

end CFSG.KD.OrdHN

end
