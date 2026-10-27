module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAssembly
public import CFSG.Sporadic.Co1Block.Thirteen
public import CFSG.Sporadic.HNOddCore.CTILocal

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

theorem co1LocalComponentsInput_holds : Co1LocalComponentsInput := fun _ _ e _ ht B hB =>
  Sporadic.Co1Block.cti_co1_involution_local_components_simple_quotient_divisible_by_thirteen
    ⟨e⟩ ht B hB

theorem hnLocalComponentsInput_holds : HNLocalComponentsInput := fun _ _ e a ha B hB =>
  Sporadic.HNOddCore.cti_hn_involution_local_components_simple_quotient_order e a ha B hB

theorem sporadicCase_Co1 : SporadicCase .Co1 :=
  sporadicCase_Co1_of_inputs co1LocalComponentsInput_holds

theorem almostSimpleRestricted_sporadicUnrestricted_of_remaining (hFour : FourExactOuterInput)
    (hLy : LyOuterTrivialInput) (hFi22 : Fi22OuterComponentsInput)
    (hFi24 : Fi24primeOuterComponentsInput) (hJ4 : J4NoComponentsInput) (hB : SporadicCase .B)
    (hM : SporadicCase .M) : AlmostSimpleRestricted SporadicUnrestricted :=
  almostSimpleRestricted_sporadicUnrestricted_of_inputs co1LocalComponentsInput_holds
    hnLocalComponentsInput_holds hFour hLy hFi22 hFi24 hJ4 hB hM

end CFSG.ComponentClassification.RestrictedStd.Spor
