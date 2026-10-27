module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

@[expose] def KDM22 : Prop :=
  ∀ (F : Type) [Group F] [Finite F], IsSimpleGroup F → CFSG.Blueprint.Catalog F →
    ∀ α : MulAut F, α ≠ 1 → α * α = 1 →
    ∀ K : Subgroup F, (∀ k ∈ K, α k = k) → IsSimpleGroup K → Nat.card K = 443520 →
      (∀ x : F, α x = x → ∀ k ∈ K, x * k * x⁻¹ ∈ K) →
      Nat.card {x : F // α x = x} ≤ 4 * 443520 → False

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
