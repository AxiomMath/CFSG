module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EBridge
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EGSide

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem lemma65_of_inputs (h30 : Input30_2) (hk : InputKType) (h515 : Lemma515)
    (hJ : InputJNormalA) : Lemma65 := by
  intro G _ _ m hS hC B hB b L A hw Q hQ hQ8
  obtain ⟨h81, hexp, hcomm, hA, hF⟩ := bridge_facts hC hB hw
  exact lemma65_of_gSide h81 hexp hcomm hA hF hQ8
    (gSideK_of_inputs h30 hk h515 hS hC hB hw hQ hQ8)
    (gSideJ_of_inputs h30 hk h515 hJ hS hC hB hw hQ hQ8)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
