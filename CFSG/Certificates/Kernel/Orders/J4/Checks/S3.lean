module

public import CFSG.Certificates.Kernel.Orders.BlockChecks
public import CFSG.Certificates.Kernel.Orders.J4.Checks.Tab
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdJ4

open CFSG.KC.Ord

theorem s3_pr : regsIn S3.PR 3 0xe27 = true := by quickRfl

theorem s3_bl : blocksOK S3.BL 3 3 = true := by quickRfl

theorem s3_pw : pwOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) S3.PR S3.PW 3 3 0xe27 = true := by
  quickRfl

theorem s3_pc :
    Nat.beq (runPc RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE S3.PR S3.PW 3 3 2 S3.PC 1) (Nat.add 1 3) = true := by
  quickRfl

@[expose] noncomputable def PT3 (b : Nat) : Nat → Nat := [PT3_0, PT3_1, PT3_2].getD b PT3_0

@[expose] def bf3 (b : Nat) : Bool :=
  blkBF RW (vecR 2 8 0x380 0x70 6 LV HV RM) (validM 2 0x380 LV HV) S3.PR S3.BL 3 PT3 b

@[expose] def bt3 (b : Nat) : Bool :=
  blkBT RW (vecR 2 8 0x380 0x70 6 LV HV RM) S3.PR S3.BL 3 PT3 S3.TC S3.N b

@[expose] def bs3 (b : Nat) : Bool := blkBS PT3 S3.N S3.SC S3.SS b

@[expose] def bn3 (b : Nat) : Bool := blkBN 3 S3.BL S3.N S3.SS b

end CFSG.KD.OrdJ4

#kc_each CFSG.KD.OrdJ4.bf3 0 3
#kc_each CFSG.KD.OrdJ4.bt3 0 3
#kc_each CFSG.KD.OrdJ4.bs3 0 3
#kc_each CFSG.KD.OrdJ4.bn3 0 3

namespace CFSG.KD.OrdJ4

#kc_forall_chunks S3.BF.all (fun b => bf3 b = true) 3 CFSG.KD.OrdJ4.bf3 1
#kc_forall_chunks S3.BT.all (fun b => bt3 b = true) 3 CFSG.KD.OrdJ4.bt3 1
#kc_forall_chunks S3.BS.all (fun b => bs3 b = true) 3 CFSG.KD.OrdJ4.bs3 1
#kc_forall_chunks S3.BN.all (fun b => bn3 b = true) 3 CFSG.KD.OrdJ4.bn3 1

end CFSG.KD.OrdJ4

end
