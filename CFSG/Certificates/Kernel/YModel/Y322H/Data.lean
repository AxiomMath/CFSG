module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM322H
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.YMY322H "CFSG/Certificates/Kernel/YModel/Y322H/data/nets.items.gz" 92872 17141650588042406549
  N[8] B0 M0_[7] R0_[7] Z0_[7]

namespace CFSG.KD.YMY322H

open CFSG.KC.YModel

#kc_select CFSG.KD.YMY322H Nf N 8

@[expose] noncomputable def T0_0 : Nat := N0
@[expose] noncomputable def T0_1 : Nat := N1
@[expose] noncomputable def T0_2 : Nat := N2
@[expose] noncomputable def T0_3 : Nat := N3
@[expose] noncomputable def T0_4 : Nat := N4
@[expose] noncomputable def T0_5 : Nat := N5
@[expose] noncomputable def T0_6 : Nat := N6
@[expose] noncomputable def T0_7 : Nat := N7
#kc_select CFSG.KD.YMY322H T0 T0_ 8
#kc_select CFSG.KD.YMY322H M0 M0_ 7
#kc_select CFSG.KD.YMY322H R0 R0_ 7
#kc_select CFSG.KD.YMY322H Z0 Z0_ 7
@[expose] noncomputable def WP0 (_ : Nat) : Nat := 0
@[expose] noncomputable def WL0 (_ : Nat) : Nat := 0

@[expose] def rels : List (List Nat) :=
  [[0, 0],
    [1, 1],
    [2, 2],
    [3, 3],
    [4, 4],
    [5, 5],
    [6, 6],
    [7, 7],
    [0, 1, 0, 1, 0, 1],
    [0, 2, 0, 2],
    [0, 3, 0, 3],
    [0, 4, 0, 4, 0, 4],
    [0, 5, 0, 5],
    [0, 6, 0, 6, 0, 6],
    [0, 7, 0, 7],
    [1, 2, 1, 2, 1, 2],
    [1, 3, 1, 3],
    [1, 4, 1, 4],
    [1, 5, 1, 5],
    [1, 6, 1, 6],
    [1, 7, 1, 7],
    [2, 3, 2, 3, 2, 3],
    [2, 4, 2, 4],
    [2, 5, 2, 5],
    [2, 6, 2, 6],
    [2, 7, 2, 7],
    [3, 4, 3, 4],
    [3, 5, 3, 5],
    [3, 6, 3, 6],
    [3, 7, 3, 7],
    [4, 5, 4, 5, 4, 5],
    [4, 6, 4, 6],
    [4, 7, 4, 7],
    [5, 6, 5, 6],
    [5, 7, 5, 7],
    [6, 7, 6, 7, 6, 7],
    [0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7, 0, 1, 2, 0, 4, 5, 0, 6, 7]]

end CFSG.KD.YMY322H

end
