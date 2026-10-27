module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def HeSuzONNoAltEight : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (NativeSporadic.IsSporadic S .He ∨ NativeSporadic.IsSporadic S .Suz ∨
      NativeSporadic.IsSporadic S .ONan) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ D : Subgroup ↥(fixedSubgroup σ), IsComponent D →
      ¬ Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 8))

end CFSG.ComponentClassification.CatFC
