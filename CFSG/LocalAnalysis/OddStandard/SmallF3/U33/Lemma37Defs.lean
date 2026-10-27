module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

section Defs

variable {G : Type*} [Group G]

@[expose] def twoThreeCore (Y : Subgroup G) : Subgroup G :=
  ((CFSG.pCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map
    Y.subtype

end Defs

end CFSG.OddStandard.SmallF3.HarrisU33
