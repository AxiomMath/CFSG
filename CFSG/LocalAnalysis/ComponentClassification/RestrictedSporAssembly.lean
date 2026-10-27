module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuCase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseRu
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseCo3
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseCo2
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseCo1
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseTh
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseFi23
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseLy
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseHN
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseMcL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseJ4

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG CFSG.Blueprint

theorem almostSimpleRestricted_sporadicUnrestricted_of_inputs
    (hCo1 : Co1LocalComponentsInput) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (hLy : LyOuterTrivialInput)
    (hFi22 : Fi22OuterComponentsInput) (hFi24 : Fi24primeOuterComponentsInput)
    (hJ4 : J4NoComponentsInput) (hB : SporadicCase .B) (hM : SporadicCase .M) :
    AlmostSimpleRestricted SporadicUnrestricted := by
  refine almostSimpleRestricted_sporadicUnrestricted_of_cases fun s hs => ?_
  cases s with
  | M11 => exact sporadicCase_M11
  | M22 => exact sporadicCase_M22
  | M23 => exact sporadicCase_M23
  | M24 => exact sporadicCase_M24
  | J4 => exact sporadicCase_J4_of_inputs hJ4
  | McL => exact sporadicCase_McL
  | Ru => exact sporadicCase_Ru
  | Co1 => exact sporadicCase_Co1_of_inputs hCo1
  | Co2 => exact sporadicCase_Co2
  | Co3 => exact sporadicCase_Co3
  | Fi22 => exact sporadicCase_Fi22_of_inputs hFi22
  | Fi23 => exact sporadicCase_Fi23
  | Fi24Prime => exact sporadicCase_Fi24prime_of_inputs hFi24
  | HN => exact sporadicCase_HN_of_inputs hHN hFour
  | Ly => exact sporadicCase_Ly_of_inputs hLy
  | Th => exact sporadicCase_Th
  | B => exact hB
  | M => exact hM
  | M12 | J1 | J2 | J3 | HS | He | Suz | ONan => exact absurd (by decide) hs

end CFSG.ComponentClassification.RestrictedStd.Spor
