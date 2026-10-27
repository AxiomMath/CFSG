module

public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuter
public import CFSG.Sporadic.HNOddCore.OuterFix

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem hnOuterFixInput : HNOuterFixInput := fun _ _ e α hα hout =>
  Sporadic.HNOddCore.hn_outer_involution_fixSub e α hα hout

theorem fourExactOuterInput_of_BM
    (hB : ∀ (S : Type) [Group S], Nonempty (S ≃* NativeSporadic.B) → ∀ α : MulAut S, α ∈ inner S)
    (hM : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → Nonempty (S ≃* NativeSporadic.M) →
      ∀ α : MulAut S, α ∈ inner S) :
    FourExactOuterInput :=
  fourExactOuterInput_of_parts hnOuterFixInput hB hM

end CFSG.ComponentClassification.RestrictedStd.Spor
