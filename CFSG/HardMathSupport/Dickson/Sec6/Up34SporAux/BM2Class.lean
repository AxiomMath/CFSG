module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeB
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMLeaves
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.AltDown
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM2

open CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator.YS08 CFSG.HardMathSupport.Dickson.Sec6.BM

@[expose] def M3BClass : Prop :=
  ∀ x : Gmat, orderOf x = 3 → ¬ InvertedByTwoA x → IsConj x tbw

end CFSG.HardMathSupport.Dickson.Sec6.BM2
