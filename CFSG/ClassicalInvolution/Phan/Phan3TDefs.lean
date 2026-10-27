module

public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan

@[expose] def AdjacentTripleBlocks (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] {X : Type} [Group X] {n : ℕ} (U : Fin n → Subgroup X)
    (W : Fin n → Fin n → Subgroup X) : Prop :=
  ∀ i j k : Fin n, (j : ℕ) = i + 1 → (k : ℕ) = j + 1 →
    ∃ θ : Su K p f 4 →* X, θ.range = W i j ⊔ W j k ∧ θ.ker ≤ Subgroup.center (Su K p f 4) ∧
      (blockEmb2 K p f 3 0).range.map θ = U i ∧ (blockEmb2 K p f 3 1).range.map θ = U j ∧
      (blockEmb2 K p f 3 2).range.map θ = U k

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]
  {n : ℕ} {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X}

end CFSG.ClassicalInvolution.Phan.Q3G
