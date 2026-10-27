module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralH360CompTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Lang.E6Descent CFSG.GroupActions
open scoped Pointwise


theorem twE6ToralLangSetup_holds : TwE6ToralLangSetup := by
  intro n K _ _ hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg hn0 htorus Kc hKc
    hnorm h360
  obtain ⟨S, a, D, hq, hT, hap, hpow, h1, hwd⟩ :=
    nonempty_twE6ToralLangComp n K hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg hn0
      htorus Kc hKc hnorm
  exact ⟨S, a, D.i, D.e, D.y, hwd, hq, hT, hap, hpow, h1, D.hyZ, D.hyF, D.hyStab, D.hQS,
    D.centerQuot_ne_360 h360, D.hact⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
