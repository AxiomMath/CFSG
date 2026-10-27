module

public import CFSG.Certificates.Kernel.YModel.Y322H.Data
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.YMY322H.Rows.C0P "CFSG/Certificates/Kernel/YModel/Y322H/data/rows/C_0_P.bin" 146 14729435802462631625
#kc_repo #kc_items_root CFSG.KD.YMY322H.Rows.L0P "CFSG/Certificates/Kernel/YModel/Y322H/data/rows/L_0_P.bin" 166 7020603650258149229
#kc_repo #kc_items_root CFSG.KD.YMY322H.Rows.L1P "CFSG/Certificates/Kernel/YModel/Y322H/data/rows/L_1_P.bin" 87 13862193613584769252
#kc_repo #kc_items_root CFSG.KD.YMY322H.Rows.R0P "CFSG/Certificates/Kernel/YModel/Y322H/data/rows/R_0_P.bin" 554 15638716506325230557
#kc_repo #kc_items_root CFSG.KD.YMY322H.Rows.X0P "CFSG/Certificates/Kernel/YModel/Y322H/data/rows/X_0_P.bin" 125 15395900928474326940

namespace CFSG.KD.YMY322H.Rows

open CFSG.KD.YMY322H CFSG.KC.YModel

@[expose] noncomputable def chkC0 (g : Nat) : Bool :=
  levelOK (C0P (4 * g + 0)) (C0P (4 * g + 1)) (C0P (4 * g + 2)) T0 B0 R0 M0 Z0 (C0P (4 * g + 3))

@[expose] noncomputable def chkL0 (g : Nat) : Bool :=
  letOK (L0P (4 * g + 0)) (L0P (4 * g + 1)) (CFSG.KD.YM322H.F (L0P (4 * g + 2))) (Nf (L0P (4 * g + 3)))

@[expose] noncomputable def chkL1 (g : Nat) : Bool :=
  Nat.beq (lget CFSG.KD.YM322H.El (L1P (2 * g + 0))) (L1P (2 * g + 1))

@[expose] noncomputable def chkR0 (g : Nat) : Bool :=
  weqK (R0P (3 * g + 0)) (R0P (3 * g + 1)) Nf (lgetL rels (R0P (3 * g + 2))) []

@[expose] noncomputable def chkX0 (g : Nat) : Bool :=
  Nat.beq (fieldAt (X0P (4 * g + 0)) (CFSG.KD.YM322H.F (X0P (4 * g + 1))) (X0P (4 * g + 2)))
    (X0P (4 * g + 3))

end CFSG.KD.YMY322H.Rows

end
