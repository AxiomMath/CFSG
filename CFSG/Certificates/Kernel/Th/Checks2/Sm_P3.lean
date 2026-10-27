module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P3.f0P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P3_0_P.bin" 40 3994507331646493388
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P3.f0L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P3_0_L0.bin" 241 13285731317769104573
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P3.f0O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P3_0_O0.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P3.f0I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P3_0_I.bin" 19 14667893835390355763

namespace CFSG.KD.ThS.Rows_Sm_P3

@[expose] noncomputable def f0l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_P3.f0L0 (CFSG.KD.ThS.Rows_Sm_P3.f0O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_P3.f0O0 g) (CFSG.KD.ThS.Rows_Sm_P3.f0O0 g)

@[expose] noncomputable def f0 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runSlp CFSG.KD.ThS.RBp3 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThS.Rows_Sm_P3.f0l0 g) (CFSG.KD.ThS.Rows_Sm_P3.f0P (2 * g + 0)))
    (CFSG.KD.ThS.Rows_Sm_P3.f0P (2 * g + 1))

end CFSG.KD.ThS.Rows_Sm_P3

#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_P3.f0 4 as CFSG.KD.ThS.sp3_ names CFSG.KD.ThS.Rows_Sm_P3.f0I
  eval CFSG.KD.ThS.Rows_Sm_P3.f0P CFSG.KD.ThS.Rows_Sm_P3.f0l0

end
