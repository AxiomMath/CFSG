module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
import CFSG.Certificates.Kernel.Bounds.LoadGz
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Common.LceS
public import Certificates.Data.Kernel.LceSSeg
public import Certificates.Data.Kernel.Multipliers.LabZ
public import Certificates.Data.Kernel.Multipliers.Mono

#kc_repo #kc_nat_items_gz CFSG.KD.M12C "CFSG/Certificates/Kernel/Bounds/M12CovAlt/data/C.items.gz" 206895 14135993359727827001
  B[17] INV INV8 nC WT[337] RT[5] ST[1] HS LBB[67] TG[337] BIAS QQ HIGH TOP
#kc_repo #kc_items_gz CFSG.KD.M12C.JF "CFSG/Certificates/Kernel/Bounds/M12CovAlt/data/JF.bin.gz" 65203 14293444775739832793
#kc_repo #kc_items_gz CFSG.KD.M12C.CY "CFSG/Certificates/Kernel/Bounds/M12CovAlt/data/cyc.bin.gz" 738 4943976837493002512
#kc_selectT CFSG.KD.M12C blk B 17
#kc_selectT CFSG.KD.M12C selWT WT 337
#kc_select CFSG.KD.M12C selRT RT 5
#kc_select CFSG.KD.M12C selST ST 1
#kc_selectT CFSG.KD.M12C lblk LBB 67
#kc_selectT CFSG.KD.M12C TG TG 337
#kc_repo #kc_nat_items_gz CFSG.KD.M12M "CFSG/Certificates/Kernel/Bounds/M12CovAlt/data/M.items.gz" 193 4764344199562952776
  TBL

public section

namespace CFSG.KD.M12C

@[expose] noncomputable def LB (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (lblk (Nat.shiftRight i (nat_lit 6))) (Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 288)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 288)) (nat_lit 1))

@[expose] noncomputable def Cs : List Nat := CFSG.KC.LceSeg.seg JF (nat_lit 134) (nat_lit 0)

@[expose] noncomputable def cyc (j : Nat) : Bool :=
  CFSG.KC.LabZ.cycZ blk selWT LB BIAS (nat_lit 4263) (CY (Nat.mul (nat_lit 4) j))
    (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 1))) (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 2)))
    (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 3)))

end CFSG.KD.M12C

namespace CFSG.KD.M12M

@[expose] noncomputable def Tab (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TBL (Nat.mul i (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def Cst (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq k (nat_lit 2))

@[expose] def Rc : List (List Nat) :=
  [[3, 0, 3, 0, 3, 0], [0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2], [0, 2, 2, 0, 3, 0, 0, 2, 0, 0, 2, 2]]

@[expose] def Wc : List (List Nat) :=
  [[1, 1, 3, 0, 2, 2, 1, 3, 3, 0, 0, 3, 1, 3, 1, 2, 0, 0, 2, 1, 1, 2, 2, 0, 3],
    [3, 1, 1, 3, 0, 0, 2, 2, 2, 1, 3, 0, 2, 0, 0, 1, 2, 0, 3, 3, 3, 1, 1]]

@[expose] noncomputable def pt (x : Nat) : Bool :=
  CFSG.KC.Mono.pointOK Tab (nat_lit 2) (nat_lit 12) (nat_lit 2) Cst Rc Wc x

end CFSG.KD.M12M

end
