module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModel
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModel
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

@[expose] def yArr : Array ℕ := compA 276 (compA 276 (genArr 0) (genArr 2)) (genArr 4)
@[expose] def eaArr : Array ℕ := compA 276 (genArr 4) (genArr 0)
@[expose] def bcbArr : Array ℕ := posArr [1, 2, 1]
@[expose] def kpArr : Array ℕ := posArr kpWord
@[expose] def uArr : Array ℕ := compA 276 bcbArr (genArr 3)

end CFSG.EvenSmallLie.SympSix.Co3Ident
