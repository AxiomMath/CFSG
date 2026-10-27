module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KThirty2A
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KThirty2B

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem input30_2_holds : Input30_2 := fun K _ _ h =>
  ⟨rank_le_nine_of_isLThreeEps K h, sylow_of_fused_of_isLThreeEps K h⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
