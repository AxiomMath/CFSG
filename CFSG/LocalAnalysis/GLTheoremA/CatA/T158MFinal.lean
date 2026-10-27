module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MS15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MInn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped commutatorElement

section Final

theorem t158MainFact_of_rest (hTab : CFSG.HardMathSupport.Dickson.BMRows.I1416Chev2SporListK)
    (hL34 : T158L34NoFG) (hInn : T158InnElemOn t158FamTwo) (hF15 : I171.I171ShapeFact15)
    (hA : T158ShapeLieOn t158ShapeA) (hTwA : T158ShapeLieOn t158ShapeTwA)
    (hE6 : T158ShapeLieOn t158ShapeE6) (hTwE6 : T158ShapeLieOn t158ShapeTwE6)
    (hU6 : T158TailOn t158FamU6) (hTE6 : T158TailOn t158FamTE6) : T158MainFact :=
  t158MainFact_of_gaps t158m_falseOn_cyc t158m_falseOn_alt (t158m_noOn_spor hTab hL34) t158m_falseOn_odd
    (t158InnOn_of_elem hInn) (t158Shape15_of_fact15 hF15) hA hTwA hE6 hTwE6 hU6 hTE6

end Final

end CFSG.LocalAnalysis.GLTheoremA.T158

end
