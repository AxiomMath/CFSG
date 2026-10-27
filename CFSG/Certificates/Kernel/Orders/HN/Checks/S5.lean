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

theorem s5_pr : regsIn S5.PR (nat_lit 6) (nat_lit 799) = true := by quickRfl

theorem s5_bl : blocksOK S5.BL (nat_lit 3) (nat_lit 6) = true := by quickRfl

theorem s5_fl : flagOK MUL (validM (nat_lit 5) (nat_lit 0x38245) L H) (nat_lit 13) (nat_lit 0x6c1)
    (nat_lit 0x85) ONE UP FC5 FCi5 = true := by
  quickRfl

theorem s5_uni_0 : uniOK RW MUL (nat_lit 13) ONE UP FC5 FCi5 S5.PR (nat_lit 0) (nat_lit 6) = true := by
  quickRfl

@[expose] noncomputable def PT5 (b : Nat) : Nat → Nat := [PT5_0, PT5_1, PT5_2].getD b PT5_0

@[expose] def bf5 (b : Nat) : Bool :=
  blkBF RW VEC (validM (nat_lit 5) (nat_lit 0x6c1) LV HV) S5.PR S5.BL (nat_lit 6) PT5 b

@[expose] def bt5 (b : Nat) : Bool := blkBT RW VEC S5.PR S5.BL (nat_lit 6) PT5 S5.TC S5.N b

@[expose] def bs5 (b : Nat) : Bool := blkBS PT5 S5.N S5.SC S5.SS b

@[expose] def bn5 (b : Nat) : Bool := blkBN (nat_lit 5) S5.BL S5.N S5.SS b

end CFSG.KD.OrdHN

#kc_each CFSG.KD.OrdHN.bf5 0 3
#kc_each CFSG.KD.OrdHN.bt5 0 3
#kc_each CFSG.KD.OrdHN.bs5 0 3
#kc_each CFSG.KD.OrdHN.bn5 0 3

namespace CFSG.KD.OrdHN

#kc_forall_chunks S5.BF.all (fun b => bf5 b = true) 3 CFSG.KD.OrdHN.bf5 1
#kc_forall_chunks S5.BT.all (fun b => bt5 b = true) 3 CFSG.KD.OrdHN.bt5 1
#kc_forall_chunks S5.BS.all (fun b => bs5 b = true) 3 CFSG.KD.OrdHN.bs5 1
#kc_forall_chunks S5.BN.all (fun b => bn5 b = true) 3 CFSG.KD.OrdHN.bn5 1

end CFSG.KD.OrdHN

end
