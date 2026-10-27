module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdAssembly
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorFamily
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelector
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorMain
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem restrictedStandard_of_sporadic (hS : SchreierFor Blueprint.Catalog)
    (hSp : AlmostSimpleRestricted SporadicUnrestricted) : GSThmB.RestrictedStandardInput :=
  restrictedStandard_of_inputs hS OddSelector.almostSimpleRestricted_oddLinearUnrestricted
      OddClassSelector.almostSimpleRestricted_oddClassical
      EvenOrthSelector.almostSimpleRestricted_evenOrthogonal
      ExcSelector.almostSimpleRestricted_exceptionalChevalley hSp

theorem restrictedStandard_of_sporadic_inputs (hS : SchreierFor Blueprint.Catalog)
    (hBinner : ∀ (S : Type) [Group S], Nonempty (S ≃* NativeSporadic.B) →
      ∀ α : MulAut S, α ∈ inner S)
    (hMinner : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      Nonempty (S ≃* NativeSporadic.M) → ∀ α : MulAut S, α ∈ inner S)
    (hLy : Spor.LyOuterTrivialInput) (hFi22 : Spor.Fi22OuterComponentsInput)
    (hFi24 : Spor.Fi24primeOuterComponentsInput) (hJ4 : Spor.J4NoComponentsInput)
    (hB : SporadicCase .B) (hM : SporadicCase .M) : GSThmB.RestrictedStandardInput :=
  restrictedStandard_of_sporadic hS
    (Spor.almostSimpleRestricted_sporadicUnrestricted_of_remaining
      (Spor.fourExactOuterInput_of_BM hBinner hMinner) hLy hFi22 hFi24 hJ4 hB hM)

end CFSG.ComponentClassification.RestrictedStd
