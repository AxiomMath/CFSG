module

public import CFSG.LargeExtraspecial.S14SMGDefs
public import Certificates.Data.SmithL6Model
public import CFSG.LargeExtraspecial.S3Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.SmithL6 (wt adjW tvCols)
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] noncomputable def InM0 [Finite G] (S : Setting G) (c : G) : Prop :=
  ∃ h : c ∈ S.M, (⟨S.ρ ⟨c, h⟩, ⟨⟨c, h⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S

@[expose] def SmithL6Module : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2),
        (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 1395, SMG.code (φ (S.cl c)) = wt i) ∧
        (∀ i < 1395, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ SMG.code (φ (S.cl c)) = wt i) ∧
        (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
          b ≠ S.z → ∀ i j, i < 1395 → j < 1395 → SMG.code (φ (S.cl (h * S.z * h⁻¹))) = wt i →
            SMG.code (φ (S.cl b)) = wt j → (b ∈ S.Qa h ↔ adjW i j = true)) ∧
        (∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ∃ k < 1953, ∀ y ∈ S.QG,
          SMG.code (φ (S.cl (x * y * x⁻¹))) =
            CFSG.SmithE.applyCols (tvCols k) (SMG.code (φ (S.cl y))))

@[expose] def SmithL6Model : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2),
        (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 1395, SMG.code (φ (S.cl c)) = wt i) ∧
        (∀ i < 1395, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ SMG.code (φ (S.cl c)) = wt i) ∧
        (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
          b ≠ S.z → ∀ i j, i < 1395 → j < 1395 → SMG.code (φ (S.cl (h * S.z * h⁻¹))) = wt i →
            SMG.code (φ (S.cl b)) = wt j → (b ∈ S.Qa h ↔ adjW i j = true)) ∧
        (∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ∃ k < 1953, ∀ y ∈ S.QG,
          SMG.code (φ (S.cl (x * y * x⁻¹))) =
            CFSG.SmithE.applyCols (tvCols k) (SMG.code (φ (S.cl y)))) ∧
        (∀ k < 1953, ∃ m ∈ S.M, ∀ y ∈ S.QG,
          SMG.code (φ (S.cl (m * y * m⁻¹))) =
            CFSG.SmithE.applyCols (tvCols k) (SMG.code (φ (S.cl y))))

theorem smithL6Module_of_model (h : SmithL6Model) : SmithL6Module := by
  intro G _ _ _ S hw hU
  obtain ⟨φ, h1, h2, h3, h4, -⟩ := h G S hw hU
  exact ⟨φ, h1, h2, h3, h4⟩

@[expose] def SmithL6Clauses1235 (S : Setting G)
    (φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)) : Prop :=
  (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 1395, SMG.code (φ (S.cl c)) = wt i) ∧
  (∀ i < 1395, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ SMG.code (φ (S.cl c)) = wt i) ∧
  (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
    b ≠ S.z → ∀ i j, i < 1395 → j < 1395 → SMG.code (φ (S.cl (h * S.z * h⁻¹))) = wt i →
      SMG.code (φ (S.cl b)) = wt j → (b ∈ S.Qa h ↔ adjW i j = true)) ∧
  (∀ k < 1953, ∃ m ∈ S.M, ∀ y ∈ S.QG,
    SMG.code (φ (S.cl (m * y * m⁻¹))) =
      CFSG.SmithE.applyCols (tvCols k) (SMG.code (φ (S.cl y))))

@[expose] def SmithL6Clause4 (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)) : Prop :=
  ∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ∃ k < 1953, ∀ y ∈ S.QG,
    SMG.code (φ (S.cl (x * y * x⁻¹))) =
      CFSG.SmithE.applyCols (tvCols k) (SMG.code (φ (S.cl y)))

@[expose] def SmithL6E33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∉ S.QG →
        ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g

@[expose] def SmithL6E33Conj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∉ S.QG →
        IsConj S.z (g * S.z * g⁻¹ * S.z) →
          ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g

theorem smithL6E33Conj_of_E33 (h : SmithL6E33) : SmithL6E33Conj := by
  intro G _ _ _ S hw hU g hxM hxQ _
  exact h G S hw hU g hxM hxQ

@[expose] def SmithL6E34Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → IsConj S.z b → b ∈ S.QG →
        Commute (h * S.z * h⁻¹) b → b ∉ S.Qa h → ¬ IsConj S.z (h * S.z * h⁻¹ * b)

@[expose] def SmithL6E34a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ¬ IsConj S.z (x * S.z)

@[expose] def SmithL6E34b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x x' : G, IsConj S.z x → IsConj S.z x' → x ∈ S.M → x ∉ S.QG → x⁻¹ * x' ∈ S.QG →
        ∃ q ∈ S.QG, x' = q⁻¹ * x * q

@[expose] def SmithL6E23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
        x * y ∈ S.QG ∨ (x * y) ^ 2 ∈ S.QG ∨ (x * y) ^ 3 ∈ S.QG ∨ (x * y) ^ 4 ∈ S.QG

@[expose] def SmithL6E24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x h : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → h * S.z * h⁻¹ ∈ S.QG →
        x * (h * S.z * h⁻¹) * x⁻¹ ∈ S.Qa h

@[expose] def SmithL6E24Line : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
        ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ S.Qa h ∧ c ≠ S.z ∧ c ≠ h * S.z * h⁻¹ ∧
          c ≠ S.z * (h * S.z * h⁻¹)

@[expose] def SmithL6E25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
        x * y ∉ S.QG →
          ((x * y) ^ 2 ∈ S.QG → ∀ v ∈ S.commQt x ⊓ S.commQt y,
            ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ S.cl c = v) ∧
          ((x * y) ^ 3 ∈ S.QG → S.commQt x ⊓ S.commQt y = ⊥) ∧
          ((x * y) ^ 2 ∉ S.QG → (x * y) ^ 4 ∈ S.QG → S.commQt x ⊓ S.commQt y = ⊥)

@[expose] def SmithL6E23Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
        x * y ∉ S.QG → (x * y) ^ 2 ∉ S.QG → (x * y) ^ 4 ∈ S.QG → IsConj S.z ((x * y) ^ 2)

abbrev cent2 (t u : G) : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G)

@[expose] def SmithL6E23a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ t u : G, IsConj S.z t → IsConj S.z u → t ∈ S.M → u ∈ S.M → t ∉ S.QG → u ∉ S.QG →
        orderOf (t * u) = 3 →
          IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u) ∧
          Nat.card ↥(S.QG ⊓ cent2 t u) = 2 ^ 9 ∧
          S.QG ⊓ cent2 t u ≤
            Subgroup.closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u} ∧
          (∀ c ∈ cent2 t u, c ∈ S.M → (∀ q ∈ S.QG ⊓ cent2 t u, c * q = q * c) → c ∈ S.QG) ∧
          (∀ P : Subgroup G, P ≤ cent2 t u ⊓ S.M →
            (∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) → IsPGroup 2 P → P ≤ S.QG)

@[expose] def SmithL6E261 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ t u : G, IsConj S.z t → IsConj S.z u → t ∈ S.M → u ∈ S.M → t ∉ S.QG → u ∉ S.QG →
        orderOf (t * u) = 3 →
          ∃ N : Subgroup G, S.z ∈ N ∧ (∀ n ∈ N, Commute n t ∧ Commute n u) ∧
            Nonempty (N ≃* PSL(6, ZMod 2))

@[expose] def SmithL6E421Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
        Commute x S.z → Commute S.z w → Commute w y →
          ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
            orderOf (x * w) = 3 → orderOf (S.z * y) = 3 →
              ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y

end CFSG.GF2Type.SmithTypeE.L6
