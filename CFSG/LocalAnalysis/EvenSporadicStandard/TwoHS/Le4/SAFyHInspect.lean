module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyPair
public import Mathlib.GroupTheory.RegularWreathProduct

public section

namespace CFSG.EvenSporadicStandard.TwoHS

@[expose] def SignDataS9X : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (_φ : X ≃* Equiv.Perm (Fin 9)) (τ : X) (D S : Subgroup X)
    (eD : D ≃* DihedralGroup 4) (eS : S ≃* Equiv.Perm (Fin 5)), LocalPair τ D S eD eS →
    ∃ χ : X →* ℤˣ, (∀ d ∈ D, orderOf d = 4 → χ d = -1) ∧
      (∀ s : S, Equiv.Perm.sign (eS s) = -1 → χ s = -1) ∧
      (∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → χ d = 1 →
        ∀ s ∈ S, s ≠ 1 → s * s = 1 → χ s = 1 → ¬ ∃ g : X, d * s = g * τ * g⁻¹)

@[expose] def SignDataWrX : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (_φ : X ≃* RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))
    (τ : X) (D S : Subgroup X)
    (eD : D ≃* DihedralGroup 4) (eS : S ≃* Equiv.Perm (Fin 5)), LocalPair τ D S eD eS →
    ∃ χ : X →* ℤˣ, (∀ d ∈ D, orderOf d = 4 → χ d = -1) ∧
      (∀ s : S, Equiv.Perm.sign (eS s) = -1 → χ s = -1) ∧
      (∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → χ d = 1 →
        ∀ s ∈ S, s ≠ 1 → s * s = 1 → χ s = 1 → ¬ ∃ g : X, d * s = g * τ * g⁻¹)

end CFSG.EvenSporadicStandard.TwoHS
