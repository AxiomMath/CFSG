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

theorem s5_pr : regsIn S5.PR 6 0x152a = true := by quickRfl

theorem s5_bl : blocksOK S5.BL 5 6 = true := by quickRfl

theorem s5_fl : flagOK (mulR 5 12 0x534 0x6f 8 L H CM RM) (validM 5 0x2418c L H) 12 0x534 0x6f ONE
    UP FC5 FCi5 = true := by
  quickRfl

theorem s5_uni_0 : uniOK RW (mulR 5 12 0x534 0x6f 8 L H CM RM) 12 ONE UP FC5 FCi5 S5.PR 0 6 = true := by
  quickRfl

@[expose] noncomputable def PT5 (b : Nat) : Nat → Nat :=
  [PT5_0, PT5_1, PT5_2, PT5_3, PT5_4].getD b PT5_0

@[expose] def bf5 (b : Nat) : Bool :=
  blkBF RW (vecR 5 12 0x534 0x6f 8 LV HV RM) (validM 5 0x534 LV HV) S5.PR S5.BL 6 PT5 b

@[expose] def bt5 (b : Nat) : Bool :=
  blkBT RW (vecR 5 12 0x534 0x6f 8 LV HV RM) S5.PR S5.BL 6 PT5 S5.TC S5.N b

@[expose] def bs5 (b : Nat) : Bool := blkBS PT5 S5.N S5.SC S5.SS b

@[expose] def bn5 (b : Nat) : Bool := blkBN 5 S5.BL S5.N S5.SS b

end CFSG.KD.OrdLy

#kc_each CFSG.KD.OrdLy.bf5 0 5
#kc_each CFSG.KD.OrdLy.bt5 0 5
#kc_each CFSG.KD.OrdLy.bs5 0 5
#kc_each CFSG.KD.OrdLy.bn5 0 5

namespace CFSG.KD.OrdLy

#kc_forall_chunks S5.BF.all (fun b => bf5 b = true) 5 CFSG.KD.OrdLy.bf5 1
#kc_forall_chunks S5.BT.all (fun b => bt5 b = true) 5 CFSG.KD.OrdLy.bt5 1
#kc_forall_chunks S5.BS.all (fun b => bs5 b = true) 5 CFSG.KD.OrdLy.bs5 1
#kc_forall_chunks S5.BN.all (fun b => bn5 b = true) 5 CFSG.KD.OrdLy.bn5 1

end CFSG.KD.OrdLy

end
