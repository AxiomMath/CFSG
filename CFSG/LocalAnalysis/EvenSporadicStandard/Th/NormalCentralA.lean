module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.NormalCentral

public section

namespace CFSG.EvenSporadicStandard.ThStd

variable {G : Type} [Group G] [Finite G] {L S A B : Subgroup G} {z : G}

theorem ThLocalIn.le_A_of_normal (W : ThLocalIn L S A B z) {X : Subgroup G} (hXS : X ≤ S)
    (hXn : ∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ ∈ X) (hc : Nat.card X ≤ 16) : X ≤ A := fun x hx =>
  (W.mem_A_iff x).2 ⟨hXS hx, fun _ h₁ _ h₂ _ h₃ _ h₄ =>
    commutator_four_eq_one W.pgroup hXS hXn hc hx h₁ h₂ h₃ h₄⟩

end CFSG.EvenSporadicStandard.ThStd
