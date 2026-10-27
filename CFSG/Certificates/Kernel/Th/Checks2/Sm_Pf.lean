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

#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Pf.f0P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Pf_0_P.bin" 725 15171416411844588
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Pf.f0L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Pf_0_L0.bin" 3759 8062759707423164300
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Pf.f0O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Pf_0_O0.bin" 319 220876020348351543
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Pf.f0I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Pf_0_I.bin" 314 8427026448587140335

namespace CFSG.KD.ThS.Rows_Sm_Pf

@[expose] noncomputable def f0l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Pf.f0L0 (CFSG.KD.ThS.Rows_Sm_Pf.f0O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Pf.f0O0 g) (CFSG.KD.ThS.Rows_Sm_Pf.f0O0 g)

@[expose] noncomputable def f0 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runSlp CFSG.KD.ThS.RBf CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThS.Rows_Sm_Pf.f0l0 g) (CFSG.KD.ThS.Rows_Sm_Pf.f0P (2 * g + 0)))
    (CFSG.KD.ThS.Rows_Sm_Pf.f0P (2 * g + 1))

end CFSG.KD.ThS.Rows_Sm_Pf

#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Pf.f0 63 as CFSG.KD.ThS.sf_ names CFSG.KD.ThS.Rows_Sm_Pf.f0I
  eval CFSG.KD.ThS.Rows_Sm_Pf.f0P CFSG.KD.ThS.Rows_Sm_Pf.f0l0

end
