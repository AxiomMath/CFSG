module

public import CFSG.LargeExtraspecial.S3Two
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

@[expose] def SmithE34a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ¬ IsConj S.z (x * S.z)

@[expose] def SmithE34b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ x x' : G, IsConj S.z x → IsConj S.z x' → x ∈ S.M → x ∉ S.QG → x⁻¹ * x' ∈ S.QG →
        ∃ q ∈ S.QG, x' = q⁻¹ * x * q

@[expose] def SmithE23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
        x * y ∈ S.QG ∨ (x * y) ^ 2 ∈ S.QG ∨ (x * y) ^ 3 ∈ S.QG

@[expose] def SmithE24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ x h : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → h * S.z * h⁻¹ ∈ S.QG →
        x * (h * S.z * h⁻¹) * x⁻¹ ∈ S.Qa h

@[expose] def SmithE25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
        x * y ∉ S.QG →
          ((x * y) ^ 2 ∈ S.QG → ∀ v ∈ S.commQt x ⊓ S.commQt y,
            ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ S.cl c = v) ∧
          ((x * y) ^ 3 ∈ S.QG → S.commQt x ⊓ S.commQt y = ⊥)

@[expose] def SmithE24Line : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
        ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ S.Qa h ∧ c ≠ S.z ∧ c ≠ h * S.z * h⁻¹ ∧
          c ≠ S.z * (h * S.z * h⁻¹)

@[expose] def SmithE421Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
        Commute x S.z → Commute S.z w → Commute w y →
          ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
            orderOf (x * w) = 3 → orderOf (S.z * y) = 3 →
              ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y

end CFSG.LargeExtraspecial.S14
