module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def IsL2pType (X : Type) [Group X] : Prop :=
  (∃ p : ℕ, IsFermatOrMersenne p ∧ 7 < p ∧ StatedClassicalModel X .PSL 2 p 1) ∨
    StatedClassicalModel X .PSL 3 2 1

structure L2pData (X : Type) [Group X] : Prop where
  simple : IsSimpleGroup X
  nonabelian : ∃ a b : X, a * b ≠ b * a
  single_class : ∀ i j : X, orderOf i = 2 → orderOf j = 2 → ∃ k : X, k * i * k⁻¹ = j
  cent_two : ∀ i : X, orderOf i = 2 → IsPGroup 2 (Subgroup.centralizer ({i} : Set X))
  inner_three : ∀ α : MulAut X, (∃ n : ℕ, orderOf α = 3 ^ n) → ∃ k : X, ∀ x : X, α x = k * x * k⁻¹
  a4 : ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧
    3 ∣ Nat.card (Subgroup.normalizer (V : Set X)) ∧
    ∀ x ∈ Subgroup.normalizer (V : Set X),
      (∀ y ∈ Subgroup.normalizer (V : Set X), y * x = x * y) → x ^ 3 = 1 → x = 1
  nonab : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → ∃ y ∈ P, y ^ 2 ≠ 1
  aut_two : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → ∀ α : MulAut X, (∀ y ∈ P, α y = y) →
    ∀ x : X, α (α x) = x

@[expose] def L2pFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsL2pType X → L2pData X

end CFSG.QuasithinUnique
