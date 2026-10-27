module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

namespace LinCase

@[expose] def L3FixedStatement : Prop :=
  ∀ (f : ℕ), 1 ≤ f → ∀ (X : Type) [Group X], LieModel X .PSL 3 2 (2 * f) →
    (∀ 𝒜 : Subgroup (MulAut X), CFSG.IsElementaryAbelian 2 𝒜 →
      Nat.card 𝒜 ≤ 4 * Nat.card (𝒜 ⊓ (MulAut.conj : X →* MulAut X).range : Subgroup (MulAut X))) ∧
    ∀ σ : MulAut X, σ ∉ (MulAut.conj : X →* MulAut X).range → ∀ Z : Subgroup X,
      CFSG.IsElementaryAbelian 2 Z → (∀ z ∈ Z, σ z = z) → Nat.card Z ≤ (2 ^ f) ^ 2

@[expose] def L3TorusStatement : Prop :=
  ∀ (f : ℕ), 1 ≤ f → ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    LieModel A .PSL 3 2 (2 * f) →
    ∀ V : Subgroup G, IsSylowOf 2 V A → ∃ J : Subgroup G, J ≤ A ∧ J ≤ normalizer (V : Set G) ∧
      Odd (Nat.card J) ∧
      ∀ x ∈ V ⊓ centralizer (V : Set G), x ≠ 1 → ∀ y ∈ V ⊓ centralizer (V : Set G), y ≠ 1 →
        ∃ j ∈ J, j * x * j⁻¹ = y

@[expose] def L3SylowIntStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 2 n →
    ∀ P Q : Subgroup X, IsSylowOf 2 P ⊤ → IsSylowOf 2 Q ⊤ → P ≠ Q → ∀ x ∈ P ⊓ Q, x * x = 1

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
