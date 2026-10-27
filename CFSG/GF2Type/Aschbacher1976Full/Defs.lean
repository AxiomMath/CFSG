module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.GLADefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full

open CFSG CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

abbrev Hz (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

abbrev Fz (z : G) : Subgroup G := inSubgroup generalizedFitting (Hz z)

@[expose] def IsZ4Star (z : G) (w : ℕ) : Prop :=
  ∃ Z A : Subgroup G, IsCyclic Z ∧ Nat.card Z = 4 ∧ z ∈ Z ∧ IsExtraspecialPGroup 2 A ∧
    Nat.card A = 2 ^ (1 + 2 * w) ∧ A ≤ Subgroup.centralizer (Z : Set G) ∧ Z ⊔ A = Fz z ∧
    Z ⊓ A = Subgroup.zpowers z

@[expose] def BigCenterData (z : G) : Prop :=
  ∃ Y P : Subgroup G, IsCyclic Y ∧ 8 ≤ Nat.card Y ∧ z ∈ Y ∧ Y ≤ Fz z ∧
    (∀ h ∈ Hz z, conjugate Y h = Y) ∧ P ≤ Fz z ∧ (∀ h ∈ Hz z, conjugate P h = P) ∧
    (∀ x ∈ P, x ^ 4 = 1) ∧ (∀ h ∈ Hz z, (∀ x ∈ P, h * x = x * h) → h ∈ Y) ∧
    ¬ ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = Fz z

inductive Asc76Shape (z : G) : Prop
  | extraspecial (w : ℕ) : 2 ≤ w → IsExtraspecialPGroup 2 (Fz z) →
      Nat.card (Fz z) = 2 ^ (1 + 2 * w) → Asc76Shape z
  | dihedral (n : ℕ) : 3 ≤ n → Hz z = Fz z →
      Nonempty (↥(Fz z) ≃* DihedralGroup (2 ^ (n - 1))) → Asc76Shape z
  | semidihedral (n : ℕ) : 4 ≤ n → Hz z = Fz z →
      Nonempty (↥(Fz z) ≃* CFSG.Open.SemidihedralGroup n) → Asc76Shape z
  | quaternion8 : Nonempty (↥(Fz z) ≃* QuaternionGroup 2) → Asc76Shape z
  | uniqueInvolution : Hz z = Fz z → (IsCyclic (Fz z) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥(Fz z) ≃* QuaternionGroup (2 ^ (n - 2)))) → Asc76Shape z
  | bigCenter : BigCenterData z → Asc76Shape z
  | z4star (w : ℕ) : 1 ≤ w → IsZ4Star z w → Asc76Shape z

@[expose] def Asc76Setting (G : Type) [Group G] [Finite G] (z : G) : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ orderOf z = 2 ∧
    CFSG.Open.GLASymplecticType (Fz z)

@[expose] def Asc76ShapeHolds : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z → Asc76Shape z

@[expose] def PSL2Conclusion (G : Type) [Group G] : Prop :=
  ∃ p f m : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 ≤ m ∧ (p ^ f = 2 ^ m - 1 ∨ p ^ f = 2 ^ m + 1) ∧
    LieModel G .PSL 2 p f

@[expose] def Asc76LeafDihedral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z → ∀ n : ℕ, 3 ≤ n →
    Hz z = Fz z → Nonempty (↥(Fz z) ≃* DihedralGroup (2 ^ (n - 1))) → PSL2Conclusion G

@[expose] def Asc76LeafSemidihedral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z → ∀ n : ℕ, 4 ≤ n →
    Hz z = Fz z → Nonempty (↥(Fz z) ≃* CFSG.Open.SemidihedralGroup n) → False

@[expose] def Asc76LeafQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z →
    Nonempty (↥(Fz z) ≃* QuaternionGroup 2) →
      NativeSporadic.IsSporadic G .M11 ∨ LieModel G .PSL 3 3 1

@[expose] def Asc76LeafUniqueInvolution : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z → Hz z = Fz z →
    (IsCyclic (Fz z) ∨ ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥(Fz z) ≃* QuaternionGroup (2 ^ (n - 2)))) →
      False

@[expose] def Asc76LeafBigCenter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z → BigCenterData z → False

@[expose] def Asc76LeafWidthGeThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z → ∀ w : ℕ, 3 ≤ w →
    IsZ4Star z w → False

@[expose] def Asc76LeafZ4Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z → IsZ4Star z 1 →
    LieModel G .PSU 3 3 1

@[expose] def Asc76LeafZ4Q8Sq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z → IsZ4Star z 2 →
    NativeSporadic.IsSporadic G .HS

structure Asc76Inputs : Prop where
  shape : Asc76ShapeHolds
  dihedral : Asc76LeafDihedral
  semidihedral : Asc76LeafSemidihedral
  q8 : Asc76LeafQ8
  uniqueInvolution : Asc76LeafUniqueInvolution
  bigCenter : Asc76LeafBigCenter
  widthGeThree : Asc76LeafWidthGeThree
  z4q8 : Asc76LeafZ4Q8
  z4q8sq : Asc76LeafZ4Q8Sq

end CFSG.GF2Type.Aschbacher1976Full
