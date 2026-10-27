module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddOpen

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

open CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.RankThree.PartTwo.Sec19 CFSG.Fischer

section Statements

@[expose] def TwoLineGen : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → (ℓ ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ x g : C0 σ, x ^ 3 = 1 → x ≠ 1 → TriOddIsClassX σ x →
      (g * x * g⁻¹) * x = x * (g * x * g⁻¹) → g * x * g⁻¹ ∉ Subgroup.zpowers x →
      ∀ H : Subgroup (C0 σ), Subgroup.centralizer ({x} : Set (C0 σ)) ≤ H → g ∈ H → H = ⊤

@[expose] def OuterToralForm : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → (ℓ ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ β : MulAut (C0 σ), β ^ 3 = 1 → β ∉ innerAut (C0 σ) → ¬ TriOddIsGLine σ β →
      ∃ s : C0 σ, β s = s ∧ s ^ 3 = 1 ∧ TriOddIsGLine σ ((MulAut.conj s)⁻¹ * β)

end Statements

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
