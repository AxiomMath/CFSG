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

#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_2_P.bin" 106 12607590895380249823
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f2L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_2_L0.bin" 155 10555070097138023777
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f2O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_2_O0.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f2I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_2_I.bin" 19 13955131473457114412
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f6P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_6_P.bin" 121 1672241751476440430
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f6L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_6_L0.bin" 1571 6317805158930176790
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f6O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_6_O0.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f6I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_6_I.bin" 21 105332303538653624
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f7P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_7_P.bin" 387 10525827362804288936
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f7L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_7_L0.bin" 1026 8288212377495644529
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f7O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_7_O0.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f7I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_7_I.bin" 21 105332303538653624
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f8P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_8_P.bin" 251 10519202810405181672
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f8I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_8_I.bin" 19 14667893835390355763
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f10P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_10_P.bin" 30 11879755227048816522
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f10L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_10_L0.bin" 23 11984138673222169148
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f10O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_10_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f10I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_10_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f11P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_11_P.bin" 73 14187998452808087567
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f11L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_11_L0.bin" 18 11565852737450085927
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f11O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_11_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f11I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_11_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f13P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_13_P.bin" 30 16366070306378128483
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f13L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_13_L0.bin" 11 16155219642215467516
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f13O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_13_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f13I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_13_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f14P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_14_P.bin" 73 15712033818966137238
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f14L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_14_L0.bin" 9 12673807556449782749
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f14O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_14_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f14I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_14_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f16P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_16_P.bin" 30 9282862610549634123
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f16L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_16_L0.bin" 11 12568015635375854108
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f16O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_16_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f16I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_16_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f17P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_17_P.bin" 73 987997728028388229
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f17L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_17_L0.bin" 9 12673807556449782749
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f17O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_17_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y3.f17I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y3_17_I.bin" 4 14007230941556241898

namespace CFSG.KD.ThS.Rows_Sm_Y3

@[expose] noncomputable def f2l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f2L0 (CFSG.KD.ThS.Rows_Sm_Y3.f2O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f2O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f2O0 g)

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runPc CFSG.KD.ThS.RBp3 CFSG.KD.ThS.PW3 CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE CFSG.KD.ThS.PR3 (CFSG.KD.ThS.Rows_Sm_Y3.f2P (5 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y3.f2P (5 * g + 1)) (CFSG.KD.ThS.Rows_Sm_Y3.f2P (5 * g + 2))
    (CFSG.KD.ThS.Rows_Sm_Y3.f2l0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f2P (5 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f2P (5 * g + 4))

@[expose] noncomputable def f6l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f6L0 (CFSG.KD.ThS.Rows_Sm_Y3.f6O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f6O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f6O0 g)

@[expose] noncomputable def f6 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp3 CFSG.KD.ThS.PT3_0 CFSG.KD.ThS.rm CFSG.KD.ThS.PR3
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f6P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y3.f6P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3
    (CFSG.KD.ThS.Rows_Sm_Y3.f6P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f6P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f6l0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f6P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f6P (6 * g + 5))

@[expose] noncomputable def f7l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f7L0 (CFSG.KD.ThS.Rows_Sm_Y3.f7O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f7O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f7O0 g)

@[expose] noncomputable def f7 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT3_0 (CFSG.KD.ThS.Rows_Sm_Y3.f7P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y3.f7P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f7P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f7P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f7P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y3.f7P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y3.f7l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y3.f7P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y3.f7P (8 * g + 7))

@[expose] noncomputable def f8 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThS.Rows_Sm_Y3.f8P (6 * g + 0))) (Nat.pow
    (CFSG.KD.ThS.Rows_Sm_Y3.f8P (6 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3
    (CFSG.KD.ThS.Rows_Sm_Y3.f8P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f8P (6 * g + 3)))
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f8P (6 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y3.f8P (6 * g + 5)))))

@[expose] noncomputable def f10l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f10L0 (CFSG.KD.ThS.Rows_Sm_Y3.f10O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f10O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f10O0 g)

@[expose] noncomputable def f10 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp3 CFSG.KD.ThS.PT3_1 CFSG.KD.ThS.rm CFSG.KD.ThS.PR3
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f10P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y3.f10P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3
    (CFSG.KD.ThS.Rows_Sm_Y3.f10P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f10P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f10l0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f10P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f10P (6 * g + 5))

@[expose] noncomputable def f11l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f11L0 (CFSG.KD.ThS.Rows_Sm_Y3.f11O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f11O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f11O0 g)

@[expose] noncomputable def f11 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT3_1 (CFSG.KD.ThS.Rows_Sm_Y3.f11P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y3.f11P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f11P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f11P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f11P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y3.f11P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y3.f11l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y3.f11P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y3.f11P (8 * g + 7))

@[expose] noncomputable def f13l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f13L0 (CFSG.KD.ThS.Rows_Sm_Y3.f13O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f13O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f13O0 g)

@[expose] noncomputable def f13 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp3 CFSG.KD.ThS.PT3_2 CFSG.KD.ThS.rm CFSG.KD.ThS.PR3
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f13P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y3.f13P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3
    (CFSG.KD.ThS.Rows_Sm_Y3.f13P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f13P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f13l0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f13P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f13P (6 * g + 5))

@[expose] noncomputable def f14l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f14L0 (CFSG.KD.ThS.Rows_Sm_Y3.f14O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f14O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f14O0 g)

@[expose] noncomputable def f14 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT3_2 (CFSG.KD.ThS.Rows_Sm_Y3.f14P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y3.f14P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f14P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f14P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f14P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y3.f14P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y3.f14l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y3.f14P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y3.f14P (8 * g + 7))

@[expose] noncomputable def f16l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f16L0 (CFSG.KD.ThS.Rows_Sm_Y3.f16O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f16O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f16O0 g)

@[expose] noncomputable def f16 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp3 CFSG.KD.ThS.PT3_3 CFSG.KD.ThS.rm CFSG.KD.ThS.PR3
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f16P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y3.f16P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3
    (CFSG.KD.ThS.Rows_Sm_Y3.f16P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f16P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f16l0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f16P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y3.f16P (6 * g + 5))

@[expose] noncomputable def f17l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y3.f17L0 (CFSG.KD.ThS.Rows_Sm_Y3.f17O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y3.f17O0 g) (CFSG.KD.ThS.Rows_Sm_Y3.f17O0 g)

@[expose] noncomputable def f17 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT3_3 (CFSG.KD.ThS.Rows_Sm_Y3.f17P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y3.f17P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f17P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y3.f17P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (CFSG.KD.ThS.Rows_Sm_Y3.f17P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y3.f17P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y3.f17l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y3.f17P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y3.f17P (8 * g + 7))

end CFSG.KD.ThS.Rows_Sm_Y3

#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f2 4 as CFSG.KD.ThS.pc3_ names CFSG.KD.ThS.Rows_Sm_Y3.f2I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f2P CFSG.KD.ThS.Rows_Sm_Y3.f2l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f6 4 as CFSG.KD.ThS.bt3_0_ names CFSG.KD.ThS.Rows_Sm_Y3.f6I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f6P CFSG.KD.ThS.Rows_Sm_Y3.f6l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f7 4 as CFSG.KD.ThS.bs3_0_ names CFSG.KD.ThS.Rows_Sm_Y3.f7I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f7P CFSG.KD.ThS.Rows_Sm_Y3.f7l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f8 4 as CFSG.KD.ThS.bn3_ names CFSG.KD.ThS.Rows_Sm_Y3.f8I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f8P
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f10 1 as CFSG.KD.ThS.bt3_1_ names CFSG.KD.ThS.Rows_Sm_Y3.f10I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f10P CFSG.KD.ThS.Rows_Sm_Y3.f10l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f11 1 as CFSG.KD.ThS.bs3_1_ names CFSG.KD.ThS.Rows_Sm_Y3.f11I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f11P CFSG.KD.ThS.Rows_Sm_Y3.f11l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f13 1 as CFSG.KD.ThS.bt3_2_ names CFSG.KD.ThS.Rows_Sm_Y3.f13I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f13P CFSG.KD.ThS.Rows_Sm_Y3.f13l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f14 1 as CFSG.KD.ThS.bs3_2_ names CFSG.KD.ThS.Rows_Sm_Y3.f14I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f14P CFSG.KD.ThS.Rows_Sm_Y3.f14l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f16 1 as CFSG.KD.ThS.bt3_3_ names CFSG.KD.ThS.Rows_Sm_Y3.f16I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f16P CFSG.KD.ThS.Rows_Sm_Y3.f16l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y3.f17 1 as CFSG.KD.ThS.bs3_3_ names CFSG.KD.ThS.Rows_Sm_Y3.f17I
  eval CFSG.KD.ThS.Rows_Sm_Y3.f17P CFSG.KD.ThS.Rows_Sm_Y3.f17l0

theorem CFSG.KD.ThS.sd3 : CFSG.KC.Th.andB (Nat.beq (CFSG.KD.ThS.RBp3 (nat_lit 1)) (CFSG.KD.ThS.RBf
    (nat_lit 1))) (Nat.beq (CFSG.KD.ThS.RBp3 (nat_lit 2)) (CFSG.KD.ThS.RBf (nat_lit 2))) = true :=
    by
  quickRfl

theorem CFSG.KD.ThS.pw3 : CFSG.KC.Th.BigS.pwOK CFSG.KD.ThS.RBp3 CFSG.KD.ThS.PW3 CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.PR3 (nat_lit 10) (nat_lit 3) = true := by
  quickRfl

theorem CFSG.KD.ThS.gpc3 : CFSG.KC.Th.BigS.gensPcOK CFSG.KD.ThS.GL3 (nat_lit 3) CFSG.KD.ThS.PR3
    CFSG.KD.ThS.n3 (nat_lit 2080) = true := by
  quickRfl

theorem CFSG.KD.ThS.rg3 : CFSG.KC.Th.andB (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.PR3 CFSG.KD.ThS.n3
    (nat_lit 67)) (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.GL3 (nat_lit 3) (nat_lit 67)) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf3_0 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp3 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR3 (CFSG.KD.ThS.PT3_0 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (nat_lit
    5) (nat_lit 5)) (nat_lit 10) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf3_1 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp3 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR3 (CFSG.KD.ThS.PT3_1 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (nat_lit
    15) (nat_lit 5)) (nat_lit 10) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf3_2 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp3 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR3 (CFSG.KD.ThS.PT3_2 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (nat_lit
    25) (nat_lit 5)) (nat_lit 10) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf3_3 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp3 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR3 (CFSG.KD.ThS.PT3_3 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL3 (nat_lit
    35) (nat_lit 5)) (nat_lit 10) = true := by
  quickRfl

theorem CFSG.KD.ThS.bl3 : CFSG.KC.Th.BigS.blocksOK CFSG.KD.ThS.BL3 CFSG.KD.ThS.nb3 CFSG.KD.ThS.n3 =
    true := by
  quickRfl

end
