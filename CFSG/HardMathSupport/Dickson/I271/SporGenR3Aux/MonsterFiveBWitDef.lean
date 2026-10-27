module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRepDef

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.MonsterFiveB

open CFSG.Monster.AxisCount CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

structure BWit where
  tgt : ℕ
  v : Array ℕ
  inv : Bool
  c : List Native.Gen
  u : List Native.Gen
deriving Inhabited

@[expose] def bEqs (W : BWit) : List (List Native.Gen × List Native.Gen) :=
  if W.inv then
    [(rhsW W.v ++ W.c, W.c ++ W.u), (tW ++ W.u ++ tW ++ W.u, [])]
  else
    [(rhsW W.v ++ W.c, W.c ++ fiveGens[8]!)]

end CFSG.HardMathSupport.Dickson.I271.MonsterFiveB
