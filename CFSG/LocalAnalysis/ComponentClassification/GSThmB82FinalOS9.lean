module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82OS9
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB10

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem Eight2.normalizer_le_centralizer_a (hSy : CFL2Sylow) (hC : CFL2C) (hJ : CFL2J)
    (hRank : CFL2Rank) (hJo : CFSec8JOrder) (hComm : CF82L2Comm) (hCyc : CF82L2Cyc)
    (hAZ : CF82AZ) (hP : CF82A10P) (hNine : CF82L2NineAbelian) (hA : CFL2A) {X : Type}
    [Group X] [Finite X] (s : Eight2.Setting3 X) :
    normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) := by
  by_contra hNS
  exact Eight2.gs82CaseB hSy hC hJ hRank hJo hComm hCyc hAZ X s hNS
    (Eight2.gs82OS8Input hSy hC hJ hRank hJo hComm hP hNine X s hNS)
    (Eight2.gs82OS9Input hSy hC hJ hRank hJo hA X s hNS)

end CFSG.ComponentClassification.GSThmB
