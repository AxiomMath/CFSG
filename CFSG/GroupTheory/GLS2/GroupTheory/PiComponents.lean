module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Foundations.Basic

public section

namespace CFSG.SecondGeneration

variable (π : Set Nat.Primes) (G : Type*) [Group G]

@[expose] noncomputable def piResidual : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : N.Normal ∧
    ∀ x : G, ∃ m : ℕ, 0 < m ∧
      (∀ q : Nat.Primes, q.val ∣ m → q ∈ π) ∧ x ^ m ∈ N), N

structure IsPiQuasisimple : Prop where
  residual_eq_top : piResidual πᶜ G = ⊤
  quotient_isQuasisimple : CFSG.IsQuasisimple (G ⧸ CFSG.piCore πᶜ G)

structure IsPiComponent (K : Subgroup G) : Prop where
  isSubnormal : K.IsSubnormal
  isPiQuasisimple : IsPiQuasisimple π K

@[expose] noncomputable def piLayer : Subgroup G :=
  sSup {K : Subgroup G | IsPiComponent π G K}

end CFSG.SecondGeneration
