module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBWords
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenInputs

public section

namespace CFSG.KC.KDenseP.MonThreeB

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

abbrev Prs := List (List Native.Gen × List Native.Gen)

@[expose] def tri (eqs nes : Prs) : Prs := eqs ++ eqs ++ eqs ++ nes

@[expose] def e136220 : Prs := (m3bEqs.drop 0).take 8
@[expose] def e136221 : Prs := (m3bEqs.drop 8).take 18
@[expose] def e136222 : Prs := (m3bEqs.drop 26).take 17
@[expose] def e136223 : Prs := m3bEqs.drop 43
@[expose] def n136224 : Prs := m3bMoves.map fun w => (w, [])
@[expose] def n13638 : Prs := [(m7rbW, []), (m7rtbW, [])]
@[expose] def n13639 : Prs := [(dW ++ m7e2W, m7e2W ++ dW)]

end CFSG.KC.KDenseP.MonThreeB

end
