module

public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.Blueprint.Catalog
public import CFSG.LargeExtraspecial.S3Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

@[expose] def SmithE8LocalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
    ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG →
      orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
        (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2))

@[expose] def SmithE8PathInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
    ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
      Commute x S.z → Commute S.z w → Commute w y →
        ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
          ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y

@[expose] def SmithE8ThreeFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
    (∀ a b : G, IsConj S.z a → IsConj S.z b →
      orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
        (orderOf (a * b) = 4 → IsConj S.z ((a * b) ^ 2))) ∧
    ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4

@[expose] def SmithE8Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
    ChevalleyExceptionalModel G .E8 2 1

namespace E8

variable {G : Type} [Group G]

abbrev cent2 (t u : G) : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G)

@[expose] def SmithE8E33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∉ S.QG →
        ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g

@[expose] def SmithE8E33Conj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∉ S.QG →
        IsConj S.z (g * S.z * g⁻¹ * S.z) →
          ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g

theorem smithE8E33Conj_of_E33 (h : SmithE8E33) : SmithE8E33Conj := by
  intro G _ _ _ S hw hU g hxM hxQ _
  exact h G S hw hU g hxM hxQ

@[expose] def SmithE8E34Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → IsConj S.z b → b ∈ S.QG →
        Commute (h * S.z * h⁻¹) b → b ∉ S.Qa h → ¬ IsConj S.z (h * S.z * h⁻¹ * b)

@[expose] def SmithE8E34a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ¬ IsConj S.z (x * S.z)

@[expose] def SmithE8E34b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ x x' : G, IsConj S.z x → IsConj S.z x' → x ∈ S.M → x ∉ S.QG → x⁻¹ * x' ∈ S.QG →
        ∃ q ∈ S.QG, x' = q⁻¹ * x * q

@[expose] def SmithE8E23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
        x * y ∈ S.QG ∨ (x * y) ^ 2 ∈ S.QG ∨ (x * y) ^ 3 ∈ S.QG ∨ (x * y) ^ 4 ∈ S.QG

@[expose] def SmithE8E24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ x h : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → h * S.z * h⁻¹ ∈ S.QG →
        x * (h * S.z * h⁻¹) * x⁻¹ ∈ S.Qa h

@[expose] def SmithE8E24Line : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
        ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ S.Qa h ∧ c ≠ S.z ∧ c ≠ h * S.z * h⁻¹ ∧
          c ≠ S.z * (h * S.z * h⁻¹)

@[expose] def SmithE8E25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
        x * y ∉ S.QG →
          ((x * y) ^ 2 ∈ S.QG → ∀ v ∈ S.commQt x ⊓ S.commQt y,
            ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ S.cl c = v) ∧
          ((x * y) ^ 3 ∈ S.QG → S.commQt x ⊓ S.commQt y = ⊥) ∧
          ((x * y) ^ 2 ∉ S.QG → (x * y) ^ 4 ∈ S.QG → S.commQt x ⊓ S.commQt y = ⊥)

@[expose] def SmithE8E23Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
        x * y ∉ S.QG → (x * y) ^ 2 ∉ S.QG → (x * y) ^ 4 ∈ S.QG → IsConj S.z ((x * y) ^ 2)

@[expose] def SmithE8E23a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ t u : G, IsConj S.z t → IsConj S.z u → t ∈ S.M → u ∈ S.M → t ∉ S.QG → u ∉ S.QG →
        orderOf (t * u) = 3 →
          IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u) ∧
          Nat.card ↥(S.QG ⊓ cent2 t u) = 2 ^ 33 ∧
          S.QG ⊓ cent2 t u ≤
            Subgroup.closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u} ∧
          (∀ c ∈ cent2 t u, c ∈ S.M → (∀ q ∈ S.QG ⊓ cent2 t u, c * q = q * c) → c ∈ S.QG) ∧
          (∀ P : Subgroup G, P ≤ cent2 t u ⊓ S.M →
            (∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) → IsPGroup 2 P → P ≤ S.QG)

@[expose] def SmithE8E261 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ t u : G, IsConj S.z t → IsConj S.z u → t ∈ S.M → u ∈ S.M → t ∉ S.QG → u ∉ S.QG →
        orderOf (t * u) = 3 →
          ∃ N : Subgroup G, S.z ∈ N ∧ (∀ n ∈ N, Commute n t ∧ Commute n u) ∧
            LieModel ↥N .E7 0 2 1

@[expose] def SmithE8E421Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
        Commute x S.z → Commute S.z w → Commute w y →
          ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
            orderOf (x * w) = 3 → orderOf (S.z * y) = 3 →
              ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y

end E8

end CFSG.GF2Type.SmithTypeE
