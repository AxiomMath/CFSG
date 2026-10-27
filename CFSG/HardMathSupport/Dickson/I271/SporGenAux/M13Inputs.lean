module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenAInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenInputs

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13 CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

@[expose] def m13Pairs : List (List Native.Gen × List Native.Gen) :=
  [(genD13W1 ++ genD13W3, genD13W3 ++ powL 6 genD13W1),
    (genD13W1 ++ genD13W4, genD13W4 ++ genD13W1),
    (genD13W1 ++ censusGW, censusGW ++ powL 12 thirteenZ)]

@[expose] def m13Check (_ : Unit) : Bool := agreeAll m13Pairs

theorem m13Check_eq_agreeTasks :
    m13Check () = agreeTasks (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) m13Pairs := by
  rw [m13Check, agreeAll_eq_agreeTasks]

end CFSG.HardMathSupport.Dickson.I271
