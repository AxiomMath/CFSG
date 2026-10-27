module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwConj
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwConcX
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwUC

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

theorem classify_P
    (X : Subgroup WrE) (hXP : X ≤ Pw) (hN : N0w ≤ X) (hX : GoodX X) : X = X1 ∨ X = X2 :=
  classify_of_codes hXP hN hX.swap (swap_isC4 hXP hN hX) (codeSet_ne_UC hXP hN hX)

theorem finiteCore_P
    (X : Subgroup WrE) (hXP : X ≤ Pw) (hN : N0w ≤ X) (hX : GoodX X) : ConcX X := by
  rcases classify_P X hXP hN hX with rfl | rfl
  · exact concX_X1_of_mem
  · exact concX_X2_of_mem

theorem finiteCore
    (X : Subgroup WrE) (hX : GoodX X) : ConcX X :=
  finiteCore_of_facts X hX Pw_le_wrR card_wrR card_Pw card_RA Pw_inf_ssS card_N0w finiteCore_P

end CFSG.ComponentClassification.GrSLit.L34Tw
