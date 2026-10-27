module

public import CFSG.Certificates.Kernel.Orders.BlockChecks
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.Tab
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdLy

open CFSG.KC.Ord

theorem s3_pr : regsIn S3.PR 7 0x152a = true := by quickRfl

theorem s3_bl : blocksOK S3.BL 5 7 = true := by quickRfl

theorem s3_pw : pwOK RW (mulR 5 12 0x534 0x6f 8 L H CM RM) S3.PR S3.PW 7 3 0x152a = true := by
  quickRfl

theorem s3_pc :
    Nat.beq (runPc RW (mulR 5 12 0x534 0x6f 8 L H CM RM) ONE S3.PR S3.PW 7 3 2 S3.PC 1) (Nat.add 1 7) = true := by
  quickRfl

@[expose] noncomputable def PT3 (b : Nat) : Nat → Nat :=
  [PT3_0, PT3_1, PT3_2, PT3_3, PT3_4].getD b PT3_0

@[expose] def bf3 (b : Nat) : Bool :=
  blkBF RW (vecR 5 12 0x534 0x6f 8 LV HV RM) (validM 5 0x534 LV HV) S3.PR S3.BL 7 PT3 b

@[expose] def bt3 (b : Nat) : Bool :=
  blkBT RW (vecR 5 12 0x534 0x6f 8 LV HV RM) S3.PR S3.BL 7 PT3 S3.TC S3.N b

@[expose] def bs3 (b : Nat) : Bool := blkBS PT3 S3.N S3.SC S3.SS b

@[expose] def bn3 (b : Nat) : Bool := blkBN 3 S3.BL S3.N S3.SS b

end CFSG.KD.OrdLy

#kc_each CFSG.KD.OrdLy.bf3 0 5
#kc_each CFSG.KD.OrdLy.bt3 0 5
#kc_each CFSG.KD.OrdLy.bs3 0 5
#kc_each CFSG.KD.OrdLy.bn3 0 5

namespace CFSG.KD.OrdLy

#kc_forall_chunks S3.BF.all (fun b => bf3 b = true) 5 CFSG.KD.OrdLy.bf3 1
#kc_forall_chunks S3.BT.all (fun b => bt3 b = true) 5 CFSG.KD.OrdLy.bt3 1
#kc_forall_chunks S3.BS.all (fun b => bs3 b = true) 5 CFSG.KD.OrdLy.bs3 1
#kc_forall_chunks S3.BN.all (fun b => bn3 b = true) 5 CFSG.KD.OrdLy.bn3 1

end CFSG.KD.OrdLy

end
