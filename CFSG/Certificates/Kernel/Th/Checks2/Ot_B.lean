module

public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.Data.Ot_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_2_P.bin" 412 4178361395790655521
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f2L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_2_L0.bin" 180791 5460894552749488420
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f2O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_2_O0.bin" 174 17136165674489541120
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f2I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_2_I.bin" 204 4052659037970922681
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f3P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_3_P.bin" 5702 2973512637659404665
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f3L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_3_L0.bin" 146395 18041083757641062500
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f3O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_3_O0.bin" 174 17136165674489541120
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f3I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_3_I.bin" 204 4052659037970922681
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_B.f4P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_B_4_P.bin" 86 10636998956986405440

namespace CFSG.KD.ThO.Rows_Ot_B

@[expose] noncomputable def f2l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThO.Rows_Ot_B.f2L0 (CFSG.KD.ThO.Rows_Ot_B.f2O0 (g + 1) -
    CFSG.KD.ThO.Rows_Ot_B.f2O0 g) (CFSG.KD.ThO.Rows_Ot_B.f2O0 g)

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.runClass2 CFSG.KD.ThO.CB2 CFSG.KD.ThB.LT CFSG.KD.ThB.LI CFSG.KD.ThB.TL
    CFSG.KD.ThB.VL CFSG.KD.ThB.NL (CFSG.KD.ThO.Rows_Ot_B.f2l0 g) (CFSG.KD.ThO.Rows_Ot_B.f2P (2 * g +
    0))) (CFSG.KD.ThO.Rows_Ot_B.f2P (2 * g + 1))

@[expose] noncomputable def f3l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThO.Rows_Ot_B.f3L0 (CFSG.KD.ThO.Rows_Ot_B.f3O0 (g + 1) -
    CFSG.KD.ThO.Rows_Ot_B.f3O0 g) (CFSG.KD.ThO.Rows_Ot_B.f3O0 g)

@[expose] noncomputable def f3 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat CFSG.KD.ThO.CB2)
    (CFSG.KD.ThO.Rows_Ot_B.f3P (4 * g + 0)) (CFSG.KD.ThO.Rows_Ot_B.f3P (4 * g + 1))
    (CFSG.KD.ThO.Rows_Ot_B.f3l0 g) (CFSG.KD.ThO.Rows_Ot_B.f3P (4 * g + 2)))
    (CFSG.KD.ThO.Rows_Ot_B.f3P (4 * g + 3))

@[expose] noncomputable def f4 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThO.Rows_Ot_B.f4P (2 * g + 0)))
    (CFSG.KD.ThO.Rows_Ot_B.f4P (2 * g + 1))

end CFSG.KD.ThO.Rows_Ot_B

#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_B.f2 34 as CFSG.KD.ThO.bt_ names CFSG.KD.ThO.Rows_Ot_B.f2I eval
  CFSG.KD.ThO.Rows_Ot_B.f2P CFSG.KD.ThO.Rows_Ot_B.f2l0
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_B.f3 34 as CFSG.KD.ThO.bs_ names CFSG.KD.ThO.Rows_Ot_B.f3I eval
  CFSG.KD.ThO.Rows_Ot_B.f3P CFSG.KD.ThO.Rows_Ot_B.f3l0
#kc_unfold CFSG.KD.ThO.bn CFSG.KD.ThO.Rows_Ot_B.f4 0 eval CFSG.KD.ThO.Rows_Ot_B.f4P

theorem CFSG.KD.ThO.b0 : Nat.beq (CFSG.KC.Th.DceS.mat CFSG.KD.ThO.CB2 (nat_lit 0))
    (CFSG.KC.Th.DceS.mat CFSG.KD.ThB.E1 (nat_lit 3)) = true := by
  quickRfl

theorem CFSG.KD.ThO.b1 : CFSG.KC.Th.OutS.invRank (nat_lit 12) (CFSG.KC.Th.DceS.mat CFSG.KD.ThO.CB2
    (nat_lit 0)) = true := by
  quickRfl

end
