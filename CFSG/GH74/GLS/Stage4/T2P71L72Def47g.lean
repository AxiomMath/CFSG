module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open CFSG.Blueprint

@[expose] def IVK_4_7g : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 1 ≤ n → LieModel K .G2 0 3 n → ∀ P : Sylow 3 K,
    ∀ B : Subgroup K, B ≤ (P : Subgroup K) → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      Nat.card ↥(P : Subgroup K) ≤ 3 * Nat.card ↥B → False

end CFSG.GH74.GLS.Stage4.Rest.L72
