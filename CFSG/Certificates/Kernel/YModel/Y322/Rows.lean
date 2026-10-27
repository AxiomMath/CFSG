module

public import CFSG.Certificates.Kernel.YModel.Y322.Data
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.C0P "CFSG/Certificates/Kernel/YModel/Y322/data/rows/C_0_P.bin" 174 10314267137512690002
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.C1P "CFSG/Certificates/Kernel/YModel/Y322/data/rows/C_1_P.bin" 125 2262914125001967697
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.L0P "CFSG/Certificates/Kernel/YModel/Y322/data/rows/L_0_P.bin" 166 4127852203788037512
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.L1P "CFSG/Certificates/Kernel/YModel/Y322/data/rows/L_1_P.bin" 87 14666157552006737865
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.R0P "CFSG/Certificates/Kernel/YModel/Y322/data/rows/R_0_P.bin" 554 11051234777727587260
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.W0P "CFSG/Certificates/Kernel/YModel/Y322/data/rows/W_0_P.bin" 100 3469343198039021399
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.W0L0 "CFSG/Certificates/Kernel/YModel/Y322/data/rows/W_0_L0.bin" 3405 8966309223433318135
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.W0O0 "CFSG/Certificates/Kernel/YModel/Y322/data/rows/W_0_O0.bin" 60 13853217593996313352
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.W0L1 "CFSG/Certificates/Kernel/YModel/Y322/data/rows/W_0_L1.bin" 2793 2421331767273607379
#kc_repo #kc_items_root CFSG.KD.YMY322.Rows.W0O1 "CFSG/Certificates/Kernel/YModel/Y322/data/rows/W_0_O1.bin" 60 3055501119434678242

namespace CFSG.KD.YMY322.Rows

open CFSG.KD.YMY322 CFSG.KC.YModel CFSG.KC.LceSeg

@[expose] noncomputable def chkC0 (g : Nat) : Bool :=
  levelOK (C0P (5 * g + 0)) (C0P (5 * g + 1)) (C0P (5 * g + 2)) T0 (CFSG.KD.YM322C.F (C0P (5 * g + 3)))
    R0 M0 Z0 (C0P (5 * g + 4))

@[expose] noncomputable def chkC1 (g : Nat) : Bool :=
  levelOK (C1P (4 * g + 0)) (C1P (4 * g + 1)) (C1P (4 * g + 2)) T1 B1 R1 M1 Z1 (C1P (4 * g + 3))

@[expose] noncomputable def chkL0 (g : Nat) : Bool :=
  letOK (L0P (4 * g + 0)) (L0P (4 * g + 1)) (CFSG.KD.YM322P.F (L0P (4 * g + 2))) (Nf (L0P (4 * g + 3)))

@[expose] noncomputable def chkL1 (g : Nat) : Bool :=
  Nat.beq (lget CFSG.KD.YM322P.El (L1P (2 * g + 0))) (L1P (2 * g + 1))

@[expose] noncomputable def chkR0 (g : Nat) : Bool :=
  weqK (R0P (3 * g + 0)) (R0P (3 * g + 1)) Nf (lgetL rels (R0P (3 * g + 2))) []

@[expose] noncomputable def wordW0a (g : Nat) : List Nat :=
  seg W0L0 (W0O0 (g + 1) - W0O0 g) (W0O0 g)

@[expose] noncomputable def wordW0b (g : Nat) : List Nat :=
  seg W0L1 (W0O1 (g + 1) - W0O1 g) (W0O1 g)

@[expose] noncomputable def chkW0 (g : Nat) : Bool :=
  weqK (W0P (2 * g + 0)) (W0P (2 * g + 1)) Nf (wordW0a g) (wordW0b g)

end CFSG.KD.YMY322.Rows

end
