module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM432FC
public import CFSG.Certificates.Kernel.YModel.Texts.YM432P
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Benes

public section

#kc_repo #kc_nat_items_gz CFSG.KD.YMY432F "CFSG/Certificates/Kernel/YModel/Y432F/data/plan.items.gz" 11267 14519129019501751879
  M0_[9] R0_[9] Z0_[9]

namespace CFSG.KD.YMY432F

open CFSG.KC.YModel CFSG.KC.MonsterConv.Perm

#kc_benes CFSG.KD.YMY432F N 0 10 15 fun _ c => colPlanes (CFSG.KD.YM432P.F c) 32 31671 15 0
#kc_select CFSG.KD.YMY432F Nf N 10

@[expose] noncomputable def T0_0 : Nat := N0
@[expose] noncomputable def T0_1 : Nat := N1
@[expose] noncomputable def T0_2 : Nat := N2
@[expose] noncomputable def T0_3 : Nat := N3
@[expose] noncomputable def T0_4 : Nat := N4
@[expose] noncomputable def T0_5 : Nat := N5
@[expose] noncomputable def T0_6 : Nat := N6
@[expose] noncomputable def T0_7 : Nat := N7
@[expose] noncomputable def T0_8 : Nat := N8
@[expose] noncomputable def T0_9 : Nat := N9
@[expose] noncomputable def WP0 (i : Nat) : Nat := CFSG.KD.YM432FC.F (i + 1)
@[expose] noncomputable def WL0 (i : Nat) : Nat := lget CFSG.KD.YM432FC.El (i + 1)
#kc_benes CFSG.KD.YMY432F T0_ 10 16 15 fun T j =>
  netsApply 15 (wid 15) (repU (wid 15) 15) (wordNets 15 32 T (WP0 (j - 10)) (WL0 (j - 10))) (idP 15)
#kc_select CFSG.KD.YMY432F T0 T0_ 26
#kc_select CFSG.KD.YMY432F M0 M0_ 9
#kc_select CFSG.KD.YMY432F R0 R0_ 9
#kc_select CFSG.KD.YMY432F Z0 Z0_ 9

@[expose] def rels : List (List Nat) :=
  [[0, 0],
    [1, 1],
    [2, 2],
    [3, 3],
    [4, 4],
    [5, 5],
    [6, 6],
    [7, 7],
    [8, 8],
    [9, 9],
    [0, 1, 0, 1, 0, 1],
    [0, 2, 0, 2],
    [0, 3, 0, 3],
    [0, 4, 0, 4],
    [0, 5, 0, 5, 0, 5],
    [0, 6, 0, 6],
    [0, 7, 0, 7],
    [0, 8, 0, 8, 0, 8],
    [0, 9, 0, 9],
    [1, 2, 1, 2, 1, 2],
    [1, 3, 1, 3],
    [1, 4, 1, 4],
    [1, 5, 1, 5],
    [1, 6, 1, 6],
    [1, 7, 1, 7],
    [1, 8, 1, 8],
    [1, 9, 1, 9],
    [2, 3, 2, 3, 2, 3],
    [2, 4, 2, 4],
    [2, 5, 2, 5],
    [2, 6, 2, 6],
    [2, 7, 2, 7],
    [2, 8, 2, 8],
    [2, 9, 2, 9],
    [3, 4, 3, 4, 3, 4],
    [3, 5, 3, 5],
    [3, 6, 3, 6],
    [3, 7, 3, 7],
    [3, 8, 3, 8],
    [3, 9, 3, 9],
    [4, 5, 4, 5],
    [4, 6, 4, 6],
    [4, 7, 4, 7],
    [4, 8, 4, 8],
    [4, 9, 4, 9],
    [5, 6, 5, 6, 5, 6],
    [5, 7, 5, 7],
    [5, 8, 5, 8],
    [5, 9, 5, 9],
    [6, 7, 6, 7, 6, 7],
    [6, 8, 6, 8],
    [6, 9, 6, 9],
    [7, 8, 7, 8],
    [7, 9, 7, 9],
    [8, 9, 8, 9, 8, 9],
    [0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9, 0, 1, 2, 0, 5, 6, 0, 8, 9]]

end CFSG.KD.YMY432F

end
