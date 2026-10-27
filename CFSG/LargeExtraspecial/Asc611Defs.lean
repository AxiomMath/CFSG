module

public import CFSG.Fischer.Classification.Unitary.Model

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary

namespace S14

@[expose] def AschbacherUnitaryCentStmt : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H), L.Normal → ∀ m : ℕ, 6 ≤ m →
    ∀ ψ : L ≃* PG m, centralizer (L : Set H) = ⊥ →
      ∀ a : H, a * a = 1 → a ≠ 1 → (∀ l : L, (l : H) = a → ψ l ∉ DG m) →
        ∀ U : Subgroup H, IsPGroup 2 U → a ∈ U → U ≤ centralizer ({a} : Set H) →
          (∀ c ∈ centralizer ({a} : Set H), ∀ u ∈ U, c * u * c⁻¹ ∈ U) →
            (∀ l : L, (l : H) ∈ U → ψ l ∉ DG m) → Nat.card U ≤ 8

end S14

end CFSG.LargeExtraspecial
