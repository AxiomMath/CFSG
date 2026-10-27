module

public import CFSG.GH74.Uniqueness.SU.SU4Stmts
public import CFSG.GH74.Uniqueness.SU.SU5Q8D8

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def IsE16 (E : Subgroup G) : Prop :=
  Open.IsElemAbelian 2 E ∧ Nat.card E = 16

structure Conf19 (S : Sylow 2 G) (U : Subgroup G) (x z : G) (A B R : Subgroup G) : Prop where
  z_mem : z ∈ U
  isE16_A : IsE16 A
  isE16_B : IsE16 B
  A_le : A ≤ Tsub S U
  B_le : B ≤ Tsub S U
  AB_inf : A ⊓ B = U
  T_eq : A ⊔ B = Tsub S U
  invol : ∀ t ∈ Tsub S U, orderOf t = 2 → t ∈ A ∨ t ∈ B
  B_eq : conjSub x A = B
  centA : ∀ a ∈ A, a ∉ U → centralizer ({a} : Set G) ⊓ Tsub S U = A
  R_le : R ≤ (S : Subgroup G)
  R_normal : (S : Subgroup G) ≤ normalizer (R : Set G)
  R_iso : SU5.IsQ8D8 R
  R_invol : ∀ g : G, orderOf g = 2 → (g ∈ R ↔ g ∈ U ∨ (g ∈ (S : Subgroup G) ∧ g ∉ Tsub S U))
  R_four : ∀ g : G, orderOf g = 4 → (g ∈ R ↔ g ∈ (S : Subgroup G) ∧ g ^ 2 = z)

section Finite

variable [Finite G]

structure Ctx19 (S : Sylow 2 G) (U M V : Subgroup G) (x z : G) (A B R : Subgroup G) : Prop where
  hyp : Hyp184 S U M
  conf : Conf18H S M V x z
  concl : Concl189 S U M x conf.x_mem
  c19 : Conf19 S U x z A B R

@[expose] def Lemma191Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
    (A B R : Subgroup G), Ctx19 S U M V x z A B R →
      ∀ s : G, s ∈ (S : Subgroup G) → s ∉ Tsub S U → orderOf s = 2 →
        ∀ u ∈ U, u ≠ 1 → u ≠ z → ∃ g ∈ centralizer ({z} : Set G), g⁻¹ * s * g = u

@[expose] def Lemma192Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
    (A B R : Subgroup G), Ctx19 S U M V x z A B R →
      (IsSylowIn ((Op_p'p 2 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype) R ∧
        Nonempty (↥(centralizer ({z} : Set G)) ⧸ Op_p'p 2 ↥(centralizer ({z} : Set G)) ≃*
          alternatingGroup (Fin 5))) ∧
      ¬ normalizer (R : Set G) ≤ M ∧
      ∃ _ : ((Tsub S U ⊔ centralizer ((Tsub S U : Subgroup G) : Set G)).subgroupOf
          (normalizer ((Tsub S U : Subgroup G) : Set G))).Normal,
        Nonempty (↥(normalizer ((Tsub S U : Subgroup G) : Set G)) ⧸
          ((Tsub S U ⊔ centralizer ((Tsub S U : Subgroup G) : Set G)).subgroupOf
            (normalizer ((Tsub S U : Subgroup G) : Set G))) ≃*
          Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))

@[expose] def Lemma194Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
    (A B R : Subgroup G), Ctx19 S U M V x z A B R →
      pPrimeCore 2 ↥M = ⊥ ∧
      ∀ t ∈ (S : Subgroup G), orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥

@[expose] def Cor195Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
    (A B R : Subgroup G), Ctx19 S U M V x z A B R →
      generalizedFitting ↥M = (Tsub S U).subgroupOf M ∧
      ∃ _ : ((Tsub S U).subgroupOf M).Normal,
        Nonempty ((↥M ⧸ (Tsub S U).subgroupOf M) ≃* Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))

@[expose] def Lemma196Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
    (A B R : Subgroup G), Ctx19 S U M V x z A B R →
      ∀ a ∈ A, a ∉ U →
        ((∀ g : G, orderOf g = 2 → IsConj z g ∨ IsConj a g) ∧ ¬ IsConj z a) ∧
        (∀ g ∈ (S : Subgroup G), IsConj a g ↔ ((g ∈ A ∨ g ∈ B) ∧ g ∉ U)) ∧
        (Nonempty (↥(centralizer ({a} : Set G)) ≃*
            alternatingGroup (Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
          (commutator ↥(centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype = U)

@[expose] def Lemma197Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
    (A B R : Subgroup G), Ctx19 S U M V x z A B R → Nat.card G = 2 ^ 7 * 3 ^ 4 * 5

@[expose] def Sec19FalseStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
    (h : Conf18H S M V x z), Hyp184 S U M → Concl189 S U M x h.x_mem → False

@[expose] def Thm184Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M : Subgroup G), Hyp184 S U M →
    Concl184a S M ∧ Concl184b M

end Finite

end CFSG.GH74.Uniqueness.SU.SU7
