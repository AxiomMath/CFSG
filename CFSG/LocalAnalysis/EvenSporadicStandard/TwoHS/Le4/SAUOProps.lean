module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUClass

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

@[expose] def KNotInLf (hQ : Q0Facts) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    Sect7Hyps G L f s y S₀ n → ∀ (C : ECoord G), Sect8Hyp C f n S₀ → ∀ T K : Subgroup G,
      Lemma61Out C hQ f S₀ T K →
        ∀ w ∈ T, w ∉ C.E → (∀ a ∈ C.E, a * a = 1 → w * a = a * w) → w ∈ L ⊔ zpowers y →
          (∃ g : G, w = g⁻¹ * f ^ 2 * g) → w ∉ L ⊔ zpowers f

@[expose] def Cl16OfClass (hQ : Q0Facts) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    Sect7Hyps G L f s y S₀ n → ∀ (C : ECoord G), Sect8Hyp C f n S₀ → ∀ T K : Subgroup G,
      Lemma61Out C hQ f S₀ T K →
        ∀ w ∈ T, w ∉ C.E → (∀ a ∈ C.E, a * a = 1 → w * a = a * w) → w ∈ L ⊔ zpowers y →
          (∃ m : G, m * f ^ 2 = f ^ 2 * m ∧ w = m * y * m⁻¹) → Cl16 C f w

end CFSG.EvenSporadicStandard.TwoHS
