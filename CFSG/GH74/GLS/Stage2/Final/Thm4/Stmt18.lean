module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Prop18_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail17 G z k S M →
    ∀ p : ℕ, p.Prime → p ≠ 2 → 3 ≤ pRank p ↥(Op p M) → ∀ t ∈ Op p M, orderOf t = p →
      3 ≤ pRank p ↥(Op p M ⊓ centralizer ({t} : Set G)) → centralizer ({t} : Set G) ≤ M

@[expose] def Lemma18_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (E : Subgroup G) (t : G),
    Ctx18 G z k S M p E t → ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ →
      (∀ v ∈ pPrimeCoreOf 2 (Vof M E), v ∈ normalizer (X : Set G)) → Em X = X →
        pRank 2 ↥X = 1 ∧ z ∈ X

@[expose] def Lemma18_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (E : Subgroup G) (t : G),
    Ctx18 G z k S M p E t → ∀ X : Subgroup G, (∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) → ¬ X ≤ M → X ≠ ⊤ →
      ∀ J : Subgroup G, IsCompIn X J → ¬ IsL34Quotient ↥J

@[expose] def Prop18_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), CtxP G z k S M p →
    ∀ V : Subgroup G, V ≤ Op p M → IsElementaryAbelian p ↥V → ¬ IsCyclic ↥V →
      (∀ v ∈ V, v ≠ 1 → 3 ≤ pRank p ↥(Op p M ⊓ centralizer ({v} : Set G))) →
      ∀ H : Subgroup G, IsCoatom H → zpowers z ⊔ V ≤ H →
        (Fs H ≤ M ∧ z ∈ Op 2 H) ∨
          (p = 3 ∧ Nat.card ↥V = 9 ∧ LieModel (↥(Em H) ⧸ pPrimeCore 2 ↥(Em H)) .PSL 3 2 2 ∧
            InducesUnitaryAut z (Em H) ∧
            Odd (Nat.card ↥(H ⊓ centralizer (Em H : Set G))))

@[expose] def Prop18_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), CtxP G z k S M p →
    ∀ U : Subgroup G, U ≤ Op p M → (U.subgroupOf (Op p M)).Normal → IsElementaryAbelian p ↥U →
      Nat.card ↥U = p ^ 2 → ∀ H : Subgroup G, IsCoatom H →
        ((∃ X : Subgroup G, X ≤ Fof p M U ∧ X ≠ ⊥ ∧ (∃ r : ℕ, r.Prime ∧ IsElementaryAbelian r ↥X) ∧
            normalizer (X : Set G) ≤ H) ∨
          (∃ g : G, H = conjugate M g ∧ ∃ V : Subgroup G, V ≤ Qof p M U ∧ IsElementaryAbelian p ↥V ∧
            p ^ 2 ≤ Nat.card ↥V ∧ zpowers z ⊔ V ≤ H)) → H = M

end CFSG.GH74.GLS.Stage2.Final.Thm4
