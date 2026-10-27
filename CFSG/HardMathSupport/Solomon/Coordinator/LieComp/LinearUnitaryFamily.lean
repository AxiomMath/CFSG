module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearAssembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

theorem lieCompOn_linearUnitary
    (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3) :
    LieCompOn .linearUnitary := by
  apply lieCompOn_of_exports
  intro S _ _ hs hna idx hF he β hβ
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q =>
    exact lieCompCase_linear hb hQ slFactorFacts_holds slAltSixFacts_holds hs hna r q hv he β hβ
  | twistedA r q =>
    exact lieCompCase_unitary hb hQ slFactorFacts_holds slAltSixFacts_holds suFactorFacts_holds
      suAltSixFacts_holds hs hna r q hv he β hβ
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
