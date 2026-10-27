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

theorem s11_pr : regsIn S11.PR 3 0xe27 = true := by quickRfl

theorem s11_bl : blocksOK S11.BL 2 3 = true := by quickRfl

theorem s11_pw : pwOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) S11.PR S11.PW 3 11 0xe27 = true := by
  quickRfl

theorem s11_pc :
    Nat.beq (runPc RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE S11.PR S11.PW 3 11 4 S11.PC 1) (Nat.add 1 3) = true := by
  quickRfl

@[expose] noncomputable def PT11 (b : Nat) : Nat → Nat := [PT11_0, PT11_1].getD b PT11_0

@[expose] def bf11 (b : Nat) : Bool :=
  blkBF RW (vecR 2 8 0x380 0x70 6 LV HV RM) (validM 2 0x380 LV HV) S11.PR S11.BL 3 PT11 b

@[expose] def bt11 (b : Nat) : Bool :=
  blkBT RW (vecR 2 8 0x380 0x70 6 LV HV RM) S11.PR S11.BL 3 PT11 S11.TC S11.N b

@[expose] def bs11 (b : Nat) : Bool := blkBS PT11 S11.N S11.SC S11.SS b

@[expose] def bn11 (b : Nat) : Bool := blkBN 11 S11.BL S11.N S11.SS b

end CFSG.KD.OrdJ4

#kc_each CFSG.KD.OrdJ4.bf11 0 2
#kc_each CFSG.KD.OrdJ4.bt11 0 2
#kc_each CFSG.KD.OrdJ4.bs11 0 2
#kc_each CFSG.KD.OrdJ4.bn11 0 2

namespace CFSG.KD.OrdJ4

#kc_forall_chunks S11.BF.all (fun b => bf11 b = true) 2 CFSG.KD.OrdJ4.bf11 1
#kc_forall_chunks S11.BT.all (fun b => bt11 b = true) 2 CFSG.KD.OrdJ4.bt11 1
#kc_forall_chunks S11.BS.all (fun b => bs11 b = true) 2 CFSG.KD.OrdJ4.bs11 1
#kc_forall_chunks S11.BN.all (fun b => bn11 b = true) 2 CFSG.KD.OrdJ4.bn11 1

end CFSG.KD.OrdJ4

end
