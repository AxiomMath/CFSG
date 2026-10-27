module

public import CFSG.ClassicalInvolution.Q3.Q3T6XCore
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3T6B (ExAt exAt_conj symOuter_of_exact)

theorem hypOmegaModDU_three_of_fusionMin (h : Fusion3MinBranch) : HypOmegaModDU 3 1 := by
  intro G _ _ _ K z hb
  have hm := hb.member_satU
  have hi := hb.intrinsic_satU
  exact hypOmegaModU_conjClass (MemberType.cert_sl2 3 1) hm hi
    (omega5At_of_twoElementsNormalize hm (twoElementsNormalize_of_min ⟨hm, hi⟩ (h G K z hb)))

theorem twoElementsNormalizeU_three_of_min (h : Fusion3MinAll) :
    TwoElementsNormalizeU (.sl2 3 1) :=
  fun F _ _ _ hnab _ _ hK hi =>
    twoElementsNormalize_of_min ⟨hK, hi⟩ (fusion3MinOn_of_min _ (h F hnab))

end CFSG.ClassicalInvolution.Q3.Q3T6X
