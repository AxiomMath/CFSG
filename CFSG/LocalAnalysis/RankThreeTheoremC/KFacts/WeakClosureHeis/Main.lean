module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.OuterInner
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Dispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefExceptional
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefPsp4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSL
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSU
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossExcE
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossExcTw
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossExcSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporHN
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporLy
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporCo1
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporM5
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporM7
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureFinal
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicBMData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Lie


theorem sdLie_holds : SDLie :=
  sdLie_of_tags
    (fun t => by
      cases t
      · exact sdLieDef_PSL
      · exact sdLieDef_PSU
      · exact sdLieDef_PSp sdPsp4_holds
      · exact sdLieDef_POmegaOdd
      · exact sdLieDef_POmegaPlus
      · exact sdLieDef_POmegaMinus
      · exact sdLieDef_G2 sdG2p_holds
      · exact sdLieDef_F4
      · exact sdLieDef_E6
      · exact sdLieDef_E7
      · exact sdLieDef_E8
      · exact sdLieDef_twistedE6
      · exact sdLieDef_trialityD4
      · exact sdLieDef_twistedB2
      · exact sdLieDef_twistedG2
      · exact sdLieDef_twistedF4
      · exact sdLieDef_Tits)
    (fun t => by
      cases t
      · exact sdLieCross_PSL
      · exact sdLieCross_PSU
      · exact sdLieCross_PSp
      · exact sdLieCross_POmegaOdd
      · exact sdLieCross_POmegaPlus
      · exact sdLieCross_POmegaMinus
      · exact sdLieCross_G2
      · exact sdLieCross_F4
      · exact sdLieCross_E6
      · exact sdLieCross_E7
      · exact sdLieCross_E8
      · exact sdLieCross_twistedE6
      · exact sdLieCross_trialityD4
      · exact sdLieCross_twistedB2
      · exact sdLieCross_twistedG2
      · exact sdLieCross_twistedF4
      · exact sdLieCross_Tits)

end Lie

section Spor


theorem sdSpor_holds : SDSpor :=
  sdSpor_of_pairs CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds
    sdSpor_HN5 sdSpor_Ly5 sdSpor_Co1_5 sdSpor_B5 sdSpor_M5 sdSpor_M7

end Spor

section Dichotomy


theorem sylowDichotomy_holds : SylowDichotomy :=
  sylowDichotomy_of_cases sdAlt_holds sdLie_holds sdSpor_holds

end Dichotomy

section Main


theorem kFactWeakClosureHeis_holds : Generic49U3.KFactWeakClosureHeis :=
  kFactWeakClosureHeis_of_dichotomy
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds
    GL83.I713.i_7_13_1_holds outerHeisInner_holds sylowDichotomy_holds

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
