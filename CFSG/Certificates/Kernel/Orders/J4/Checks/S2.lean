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

theorem s2_pr : regsIn S2.PR 21 0xe27 = true := by quickRfl

theorem s2_bl : blocksOK S2.BL 16 21 = true := by quickRfl

theorem s2_fl : flagOK (mulR 2 8 0x380 0x70 6 L H CM RM) (validM 2 0x18800 L H) 8 0x380 0x70 ONE
    UP FC2 FCi2 = true := by
  quickRfl

theorem s2_uni_0 : uniOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) 8 ONE UP FC2 FCi2 S2.PR 0 21 = true := by
  quickRfl

@[expose] noncomputable def PT2 (b : Nat) : Nat → Nat :=
  [PT2_0, PT2_1, PT2_2, PT2_3, PT2_4, PT2_5, PT2_6, PT2_7, PT2_8, PT2_9, PT2_10, PT2_11, PT2_12,
    PT2_13, PT2_14, PT2_15].getD b PT2_0

@[expose] def bf2 (b : Nat) : Bool :=
  blkBF RW (vecR 2 8 0x380 0x70 6 LV HV RM) (validM 2 0x380 LV HV) S2.PR S2.BL 21 PT2 b

@[expose] def bt2 (b : Nat) : Bool :=
  blkBT RW (vecR 2 8 0x380 0x70 6 LV HV RM) S2.PR S2.BL 21 PT2 S2.TC S2.N b

@[expose] def bs2 (b : Nat) : Bool := blkBS PT2 S2.N S2.SC S2.SS b

@[expose] def bn2 (b : Nat) : Bool := blkBN 2 S2.BL S2.N S2.SS b

end CFSG.KD.OrdJ4

#kc_each CFSG.KD.OrdJ4.bf2 0 16
#kc_each CFSG.KD.OrdJ4.bt2 0 16
#kc_each CFSG.KD.OrdJ4.bs2 0 16
#kc_each CFSG.KD.OrdJ4.bn2 0 16

namespace CFSG.KD.OrdJ4

#kc_forall_chunks S2.BF.all (fun b => bf2 b = true) 16 CFSG.KD.OrdJ4.bf2 1
#kc_forall_chunks S2.BT.all (fun b => bt2 b = true) 16 CFSG.KD.OrdJ4.bt2 1
#kc_forall_chunks S2.BS.all (fun b => bs2 b = true) 16 CFSG.KD.OrdJ4.bs2 1
#kc_forall_chunks S2.BN.all (fun b => bn2 b = true) 16 CFSG.KD.OrdJ4.bn2 1

end CFSG.KD.OrdJ4

end
