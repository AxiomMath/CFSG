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

theorem s2_pr : regsIn S2.PR 8 0x152a = true := by quickRfl

theorem s2_bl : blocksOK S2.BL 7 8 = true := by quickRfl

theorem s2_pw : pwOK RW (mulR 5 12 0x534 0x6f 8 L H CM RM) S2.PR S2.PW 8 2 0x152a = true := by
  quickRfl

theorem s2_pc :
    Nat.beq (runPc RW (mulR 5 12 0x534 0x6f 8 L H CM RM) ONE S2.PR S2.PW 8 2 1 S2.PC 1) (Nat.add 1 8) = true := by
  quickRfl

@[expose] noncomputable def PT2 (b : Nat) : Nat → Nat :=
  [PT2_0, PT2_1, PT2_2, PT2_3, PT2_4, PT2_5, PT2_6].getD b PT2_0

@[expose] def bf2 (b : Nat) : Bool :=
  blkBF RW (vecR 5 12 0x534 0x6f 8 LV HV RM) (validM 5 0x534 LV HV) S2.PR S2.BL 8 PT2 b

@[expose] def bt2 (b : Nat) : Bool :=
  blkBT RW (vecR 5 12 0x534 0x6f 8 LV HV RM) S2.PR S2.BL 8 PT2 S2.TC S2.N b

@[expose] def bs2 (b : Nat) : Bool := blkBS PT2 S2.N S2.SC S2.SS b

@[expose] def bn2 (b : Nat) : Bool := blkBN 2 S2.BL S2.N S2.SS b

end CFSG.KD.OrdLy

#kc_each CFSG.KD.OrdLy.bf2 0 7
#kc_each CFSG.KD.OrdLy.bt2 0 7
#kc_each CFSG.KD.OrdLy.bs2 0 7
#kc_each CFSG.KD.OrdLy.bn2 0 7

namespace CFSG.KD.OrdLy

#kc_forall_chunks S2.BF.all (fun b => bf2 b = true) 7 CFSG.KD.OrdLy.bf2 1
#kc_forall_chunks S2.BT.all (fun b => bt2 b = true) 7 CFSG.KD.OrdLy.bt2 1
#kc_forall_chunks S2.BS.all (fun b => bs2 b = true) 7 CFSG.KD.OrdLy.bs2 1
#kc_forall_chunks S2.BN.all (fun b => bn2 b = true) 7 CFSG.KD.OrdLy.bn2 1

end CFSG.KD.OrdLy

end
