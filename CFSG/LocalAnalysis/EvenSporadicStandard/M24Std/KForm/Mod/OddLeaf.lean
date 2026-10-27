module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Socle
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OddA6ModLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], OddLieType S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ D : Subgroup ↥(fixedSubgroup σ), D.Normal → Nonempty (↥D ≃* alternatingGroup (Fin 6)) →
    (∀ P : Subgroup ↥(fixedSubgroup σ), ⁅P, P⁆ = P → P ≤ D) →
    ¬ 2 ^ 6 ∣ Nat.card ↥(fixedSubgroup σ) → (∀ x : ↥(fixedSubgroup σ), orderOf x ≠ 8) →
    Z2S6Socle S

end CFSG.EvenSporadicStandard.M24Std
