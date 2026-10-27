module

public import CFSG.Open.Defs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsFourGroup (U : Subgroup G) : Prop :=
  Open.IsElemAbelian 2 U ∧ Nat.card U = 4

@[expose] def centralizerJoin (U L : Subgroup G) : Subgroup G :=
  ⨆ (u : G) (_ : u ∈ U) (_ : u ≠ 1), L ⊓ Subgroup.centralizer ({u} : Set G)

@[expose] def HasDihedralSylowTwo (X : Type*) [Group X] : Prop :=
  ∃ (S : Sylow 2 X) (n : ℕ), 2 ≤ n ∧ Nonempty ((S : Subgroup X) ≃* DihedralGroup (2 ^ (n - 1)))

@[expose] def HasSemidihedralSylowTwo (X : Type*) [Group X] : Prop :=
  ∃ (S : Sylow 2 X) (n : ℕ), 4 ≤ n ∧ Nonempty ((S : Subgroup X) ≃* SemidihedralGroup n)

@[expose] def IsSmallDihedralSimple (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    ∃ p f : ℕ, p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧
      Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p f

@[expose] def HasCyclicSylowTwo (X : Type*) [Group X] : Prop :=
  ∃ P : Sylow 2 X, IsCyclic (P : Subgroup X)

structure AschbacherKnownGroupFacts : Prop where
  dihedral_cover_generation : ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G),
    Open.IsQuasisimple L → HasDihedralSylowTwo (L ⧸ Subgroup.center L) →
    (Nat.card (Subgroup.center L)).factorization 2 ≤ 1 →
    U ≤ Subgroup.normalizer (L : Set G) → IsFourGroup U → ¬ L ≤ centralizerJoin U L →
    IsSmallDihedralSimple (L ⧸ Subgroup.center L) ∧ U ≤ L ⊔ Subgroup.centralizer (L : Set G)
  small_aut_quaternion : ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X), N.Normal →
    Subgroup.centralizer (N : Set X) = ⊥ → IsSmallDihedralSimple N →
    ∀ (Q : Subgroup X) (k : ℕ), 1 ≤ k → Nonempty (Q ≃* QuaternionGroup (2 ^ k)) →
      Open.pRank 2 (Subgroup.centralizer (Q : Set X)) ≤ 1
  dihedral_outer_involution : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (a : G),
    IsSimpleGroup L → HasDihedralSylowTwo L → a ∈ Subgroup.normalizer (L : Set G) → a ^ 2 = 1 →
    HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) →
    a ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
    (∀ K : Subgroup G, Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K →
      K ≤ Subgroup.zpowers a ⊔ L →
      K = Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ∨
        K = Subgroup.zpowers a ⊔ L) ∧
    (∀ y ∈ Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)),
      (∀ m ∈ Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)), y * m = m * y) →
      y ∈ Subgroup.zpowers a) ∧
    (∀ b ∈ Subgroup.normalizer (L : Set G), b ^ 2 = 1 →
      HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) →
      a * b ∈ L ⊔ Subgroup.centralizer (L : Set G))
  semidihedral_four_group : ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G),
    Open.IsQuasisimple L → HasSemidihedralSylowTwo L → U ≤ Subgroup.normalizer (L : Set G) →
    IsFourGroup U → ∃ u ∈ U, u ≠ 1 ∧ 2 ≤ Open.pRank 2 (L ⊓ Subgroup.centralizer ({u} : Set G))
  semidihedral_dihedral_no_cyclic_four : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (a : G), Open.IsQuasisimple L → (HasDihedralSylowTwo L ∨ HasSemidihedralSylowTwo L) →
    a ∈ Subgroup.normalizer (L : Set G) → a ^ 2 = 1 →
    ∀ P : Sylow 2 ↥(L ⊓ Subgroup.centralizer ({a} : Set G)),
      ¬ (IsCyclic (P : Subgroup ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) ∧ Nat.card P = 4)

end CFSG.ComponentClassification.AschbacherKnownGroup
