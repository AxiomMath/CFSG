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

#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P2.f0P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P2_0_P.bin" 90 10923162623320524563
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P2.f0L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P2_0_L0.bin" 503 13521999702687443427
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P2.f0O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P2_0_O0.bin" 49 13319687021087572164
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P2.f0I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P2_0_I.bin" 44 73830439279506478
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P2.f1P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P2_1_P.bin" 66 10353922470968883001
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P2.f1L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P2_1_L0.bin" 503 13521999702687443427
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P2.f1O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P2_1_O0.bin" 9 8488902115272865658
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_P2.f1I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_P2_1_I.bin" 5 16716229469519616519

namespace CFSG.KD.ThS.Rows_Sm_P2

@[expose] noncomputable def f0l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_P2.f0L0 (CFSG.KD.ThS.Rows_Sm_P2.f0O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_P2.f0O0 g) (CFSG.KD.ThS.Rows_Sm_P2.f0O0 g)

@[expose] noncomputable def f0 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runSlp CFSG.KD.ThS.RBp2 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThS.Rows_Sm_P2.f0l0 g) (CFSG.KD.ThS.Rows_Sm_P2.f0P (2 * g + 0)))
    (CFSG.KD.ThS.Rows_Sm_P2.f0P (2 * g + 1))

@[expose] noncomputable def f1l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_P2.f1L0 (CFSG.KD.ThS.Rows_Sm_P2.f1O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_P2.f1O0 g) (CFSG.KD.ThS.Rows_Sm_P2.f1O0 g)

@[expose] noncomputable def f1 (g : Nat) : Bool :=
  CFSG.KC.Th.andB (Nat.beq (CFSG.KC.Th.BigS.runMarked (CFSG.KD.ThS.Rows_Sm_P2.f1l0 g)
    (CFSG.KD.ThS.Rows_Sm_P2.f1P (4 * g + 0))) (CFSG.KD.ThS.Rows_Sm_P2.f1P (4 * g + 1)))
    (CFSG.KC.Th.BigS.allMarked CFSG.KD.ThS.PR2 (CFSG.KD.ThS.Rows_Sm_P2.f1P (4 * g + 2))
    (CFSG.KD.ThS.Rows_Sm_P2.f1P (4 * g + 3)))

end CFSG.KD.ThS.Rows_Sm_P2

#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_P2.f0 9 as CFSG.KD.ThS.sp2_ names CFSG.KD.ThS.Rows_Sm_P2.f0I
  eval CFSG.KD.ThS.Rows_Sm_P2.f0P CFSG.KD.ThS.Rows_Sm_P2.f0l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_P2.f1 1 as CFSG.KD.ThS.mk names CFSG.KD.ThS.Rows_Sm_P2.f1I eval
  CFSG.KD.ThS.Rows_Sm_P2.f1P CFSG.KD.ThS.Rows_Sm_P2.f1l0

end
