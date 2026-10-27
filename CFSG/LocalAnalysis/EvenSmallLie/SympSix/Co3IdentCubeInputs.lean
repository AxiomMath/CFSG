
module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFactsBase
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFactsBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

@[expose] def kpcArr : Array ℕ := compA 276 kpArr (genArr 2)

end CFSG.EvenSmallLie.SympSix.Co3Ident
