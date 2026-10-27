module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.EvenSporadicStandard.HSStd

@[expose] def KGA6Sq : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Catalog S → IsSimpleGroup S →
    ∀ τ : MulAut S, τ * τ = 1 → Nat.card (autCentralizer τ) ≤ 5760 →
    Nonempty (↥(commutator ↥(autCentralizer τ)) ≃* alternatingGroup (Fin 6)) →
    ∀ A : Subgroup S, CFSG.IsQuasisimple ↥A →
      Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 6)) →
      (∀ a ∈ A, ∀ b ∈ A, a * τ b = τ b * a) → False

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
