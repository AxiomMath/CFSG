module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OThm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ThreeL38

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74


theorem solomon74SpinSevenAsUsedOdd_holds : Solomon74SpinSevenAsUsedOdd :=
  solomon74SpinSevenAsUsedOdd_of_lemma38Odd lemma38Odd_holds f1Odd_holds f2bOdd_holds
    spinFactsAllOdd_holds

theorem solomon74SpinSevenAsUsedThree_holds : Solomon74SpinSevenAsUsedThree :=
  solomon74SpinSevenAsUsedThree_of_odd solomon74SpinSevenAsUsedOdd_holds

end CFSG.ComponentClassification.HarrisLit.T1.S74
