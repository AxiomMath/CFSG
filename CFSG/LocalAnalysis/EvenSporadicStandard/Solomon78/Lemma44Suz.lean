module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.Defs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def Sol78Lemma44SuzFourGroup : Prop :=
  ∀ (S : Type) [Group S], IsSporadic S .Suz →
    ∃ (E₀ H₀ : Subgroup S) (n : S),
      Nat.card E₀ = 4 ∧ (∀ e ∈ E₀, e ^ 2 = 1) ∧
      (∀ e ∈ E₀, e ≠ 1 → Nat.card (centralizer ({e} : Set S)) = 161280) ∧
      centralizer (E₀ : Set S) = H₀ ⊔ E₀ ∧ H₀ ⊓ E₀ = ⊥ ∧ H₀ ≤ centralizer (E₀ : Set S) ∧
      ⁅centralizer (E₀ : Set S), centralizer (E₀ : Set S)⁆ = H₀ ∧ ⁅H₀, H₀⁆ = H₀ ∧
      Nat.card H₀ = 20160 ∧
      orderOf n = 3 ∧ n ∈ centralizer (H₀ : Set S) ∧ n ∈ normalizer (E₀ : Set S) ∧
      ∀ e ∈ E₀, e ≠ 1 → n * e * n⁻¹ ≠ e

end CFSG.EvenSporadicStandard.Solomon78
