module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Lemma19_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail17 G z k S M →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 ≤ pRank p ↥(Op p M)

@[expose] def Lemma19_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (U : Subgroup G) (t : G),
    Ctx19 G z k S M p U t →
      (∀ x ∈ Qof p M U, t * x * t⁻¹ = x⁻¹) ∧
      (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → 2 ≤ pRank r ↥(Op r M) → ∀ x ∈ Op r M, t * x * t⁻¹ = x⁻¹)

@[expose] def Lemma19_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (U : Subgroup G) (t : G),
    Ctx19 G z k S M p U t → ((Qof p M U).subgroupOf (Op p M)).Characteristic

@[expose] def Lemma19_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (U : Subgroup G) (t : G),
    Ctx19 G z k S M p U t →
      inSubgroup (oResidual p) ⁅M, zpowers t⁆ ≤
        centralizer (Fpi {r | r.Prime ∧ r ≠ 2} M : Set G)

end CFSG.GH74.GLS.Stage2.Final.Thm4
