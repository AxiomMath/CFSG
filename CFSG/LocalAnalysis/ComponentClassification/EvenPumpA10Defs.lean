module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf

@[expose] def A10PumpLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 10)) →
    (∃ n : ℕ, 10 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HN)

end CFSG.ComponentClassification.EvenPump
