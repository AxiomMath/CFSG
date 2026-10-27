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

theorem s3_pr : regsIn S3.PR (nat_lit 6) (nat_lit 799) = true := by quickRfl

theorem s3_bl : blocksOK S3.BL (nat_lit 3) (nat_lit 6) = true := by quickRfl

theorem s3_pw : pwOK RW MUL S3.PR S3.PW (nat_lit 6) (nat_lit 3) (nat_lit 799) = true := by quickRfl

theorem s3_pc : Nat.beq (runPc RW MUL ONE S3.PR S3.PW (nat_lit 6) 3 (nat_lit 2) S3.PC 1)
    (Nat.add 1 (nat_lit 6)) = true := by
  quickRfl

@[expose] noncomputable def PT3 (b : Nat) : Nat → Nat := [PT3_0, PT3_1, PT3_2].getD b PT3_0

@[expose] def bf3 (b : Nat) : Bool :=
  blkBF RW VEC (validM (nat_lit 5) (nat_lit 0x6c1) LV HV) S3.PR S3.BL (nat_lit 6) PT3 b

@[expose] def bt3 (b : Nat) : Bool := blkBT RW VEC S3.PR S3.BL (nat_lit 6) PT3 S3.TC S3.N b

@[expose] def bs3 (b : Nat) : Bool := blkBS PT3 S3.N S3.SC S3.SS b

@[expose] def bn3 (b : Nat) : Bool := blkBN (nat_lit 3) S3.BL S3.N S3.SS b

end CFSG.KD.OrdHN

#kc_each CFSG.KD.OrdHN.bf3 0 3
#kc_each CFSG.KD.OrdHN.bt3 0 3
#kc_each CFSG.KD.OrdHN.bs3 0 3
#kc_each CFSG.KD.OrdHN.bn3 0 3

namespace CFSG.KD.OrdHN

#kc_forall_chunks S3.BF.all (fun b => bf3 b = true) 3 CFSG.KD.OrdHN.bf3 1
#kc_forall_chunks S3.BT.all (fun b => bt3 b = true) 3 CFSG.KD.OrdHN.bt3 1
#kc_forall_chunks S3.BS.all (fun b => bs3 b = true) 3 CFSG.KD.OrdHN.bs3 1
#kc_forall_chunks S3.BN.all (fun b => bn3 b = true) 3 CFSG.KD.OrdHN.bn3 1

end CFSG.KD.OrdHN

end
