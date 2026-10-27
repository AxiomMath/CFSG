module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBStr

public section

namespace CFSG.ComponentClassification.GrSLit

theorem heldTwoBCentralizerStructure : HeldTwoBCentralizerStructure :=
  ⟨HeldFix.perfect_centralizer_heT1P, fun _ hNC hN hne => HeldFix.isPGroup_of_normal_ne hNC hN hne⟩

end CFSG.ComponentClassification.GrSLit
