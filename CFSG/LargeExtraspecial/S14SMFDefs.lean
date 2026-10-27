module

public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

@[expose] def SmithE32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∉ S.QG →
        ∃ y : G, y ≠ 1 ∧ y ∈ (⁅zpowers (g * S.z * g⁻¹), S.QG⁆ : Subgroup G) ∧
          Commute (g * S.z * g⁻¹) y ∧ y ∈ S.Qa g

@[expose] def SmithE33Conj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∉ S.QG →
        IsConj S.z (g * S.z * g⁻¹ * S.z) →
          ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g

@[expose] def SmithE34Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → IsConj S.z b → b ∈ S.QG →
        Commute (h * S.z * h⁻¹) b → b ∉ S.Qa h → ¬ IsConj S.z (h * S.z * h⁻¹ * b)

end CFSG.LargeExtraspecial.S14
