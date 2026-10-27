module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint

@[expose] def AschbacherFSmith1977Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      ∀ w : ℕ,
        Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
          2 ^ (1 + 2 * w) →
        3 ≤ w →
        (∀ g : G, g⁻¹ * z * g ∈ inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)) →
          g⁻¹ * z * g = z) →
        LieModel G .PSU (w + 2) 2 1 ∨ (w = 4 ∧ NativeSporadic.IsSporadic G .Co2)

end CFSG.GF2Type
