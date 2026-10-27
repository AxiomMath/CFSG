module

public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaGen
public import CFSG.HardMathSupport.Solomon.Coordinator.I713
public import CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctorInstance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop41

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.LocalBalance

theorem theoremOne_of_frontier (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (h21 : Prop21) (h22 : Prop22)
    (h31 : Lemma31) (hgen : AlphaGenHypAll) (h45 : CaseTwoFiveEven) (hIII : Prop42CaseThree)
    (h4 : CaseFourPreUniqueness) (h81 : Prop81Core) : TheoremOne :=
  theoremOne_of_props (prop41_of_inputs h21 h22 h31)
    (prop42_of_inputs hSF hbridge h21 h22 h31 hgen h45 hIII) h4 h81

theorem theoremOne_of_frontier'
    (h21 : Prop21) (h22 : Prop22) (h31 : Lemma31)
    (h45 : CaseTwoFiveEven) (hIII : Prop42CaseThree) (h4 : CaseFourPreUniqueness)
    (h81 : Prop81Core) : TheoremOne :=
  theoremOne_of_frontier signalizerFunctorTheoremK_holds
    CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge h21 h22 h31
    (alphaGenHypAll_of_i713 i_7_13_1_pPrime_holds) h45 hIII h4 h81

end CFSG.HardMathSupport.Solomon.Coordinator
