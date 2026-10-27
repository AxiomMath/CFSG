module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM233F
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.YMY233F "CFSG/Certificates/Kernel/YModel/Y233F/data/nets.items.gz" 103716 9659555536919680557
  N[9]

namespace CFSG.KD.YMY233F

open CFSG.KC.YModel

#kc_select CFSG.KD.YMY233F Nf N 9

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
    [0, 1, 0, 1, 0, 1],
    [0, 2, 0, 2],
    [0, 3, 0, 3, 0, 3],
    [0, 4, 0, 4],
    [0, 5, 0, 5],
    [0, 6, 0, 6, 0, 6],
    [0, 7, 0, 7],
    [0, 8, 0, 8],
    [1, 2, 1, 2, 1, 2],
    [1, 3, 1, 3],
    [1, 4, 1, 4],
    [1, 5, 1, 5],
    [1, 6, 1, 6],
    [1, 7, 1, 7],
    [1, 8, 1, 8],
    [2, 3, 2, 3],
    [2, 4, 2, 4],
    [2, 5, 2, 5],
    [2, 6, 2, 6],
    [2, 7, 2, 7],
    [2, 8, 2, 8],
    [3, 4, 3, 4, 3, 4],
    [3, 5, 3, 5],
    [3, 6, 3, 6],
    [3, 7, 3, 7],
    [3, 8, 3, 8],
    [4, 5, 4, 5, 4, 5],
    [4, 6, 4, 6],
    [4, 7, 4, 7],
    [4, 8, 4, 8],
    [5, 6, 5, 6],
    [5, 7, 5, 7],
    [5, 8, 5, 8],
    [6, 7, 6, 7, 6, 7],
    [6, 8, 6, 8],
    [7, 8, 7, 8, 7, 8],
    [0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7, 0, 1, 2, 0, 3, 4, 0, 6, 7]]

end CFSG.KD.YMY233F

end
