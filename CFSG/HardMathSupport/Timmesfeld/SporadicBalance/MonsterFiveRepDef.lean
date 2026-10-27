module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

open CFSG.Monster CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native

structure RepWit where
  v : Array ℕ
  repW : List Native.Gen
  kind : Bool
  wa : List Native.Gen
  ca : List Native.Gen
  wb : List Native.Gen
  cb : List Native.Gen
deriving Inhabited

@[expose] def tW : List Native.Gen := [.rho (false, 0, 191)]

@[expose] def repEqs (R : RepWit) : List (List Native.Gen × List Native.Gen) :=
  if R.kind then
    [(R.repW, rhsW R.v), (R.wa ++ R.wa, []), (R.wa ++ R.repW ++ R.wa ++ R.repW, []),
      (tW ++ R.ca, R.ca ++ R.wa)]
  else
    [(R.repW, rhsW R.v), (R.wa ++ R.wa, []), (R.wb ++ R.wb, []), (R.wa ++ R.repW, R.repW ++ R.wa),
      (R.wb ++ R.repW, R.repW ++ R.wb), (R.wa ++ R.wb, R.wb ++ R.wa), (tW ++ R.ca, R.ca ++ R.wa),
      (tW ++ R.cb, R.cb ++ R.wb)]

@[expose] def repMove (R : RepWit) : Bool :=
  R.kind || EdgeNoncomm.moveCheck (R.wa ++ R.wb) (aV ())

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
