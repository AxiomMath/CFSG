module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Choice10_exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∃ (T U : Subgroup G) (t g : G), Choice10 G z k S M T U t g

@[expose] def Remark10I_C2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → ¬ TypeOneCase G k → ∀ H R : Subgroup G, T ≤ H → HOK k T U H → Fs H = Op p H →
      MaxIn {R' : Subgroup G | R0 k p T U H R'} R → H ≤ normalizer ((kInfty R : Subgroup G) : Set G)

@[expose] def Prop10_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → ∀ R N : Subgroup G, R ≠ ⊥ → IsPGroup p ↥R → R ≤ M → T ≤ normalizer (R : Set G) →
      ¬ Q ⊓ normalizer (R : Set G) ≤ Cen z → IsCoatom N → Q ⊓ normalizer (R : Set G) ≤ N → T ≤ N → Fs N = Op p N

@[expose] def Lemma10_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → ∀ H H' : Subgroup G, H ≠ ⊤ → H' ≠ ⊤ → HOK k T U H → HOK k T U H' →
      (H ≤ H' → ∀ R : Subgroup G, R0 k p T U H R → R0 k p T U H' R) ∧
      (∀ R : Subgroup G, R0 k p T U H R → R0 k p T U (H ⊓ normalizer (R : Set G)) R ∧
        (MaxIn {R' : Subgroup G | R0 k p T U H R'} R ↔
          MaxIn {R' : Subgroup G | R0 k p T U (H ⊓ normalizer (R : Set G)) R'} R)) ∧
      (∀ R R₀ : Subgroup G, R0 k p T U H R → R₀ ≤ R → R₀ ≠ ⊥ → Subgroup.Characteristic (R₀.subgroupOf R) →
        R0 k p T U H R₀)

@[expose] def Lemma10_2b_C2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → ¬ TypeOneCase G k → ∀ H : Subgroup G, H ≠ ⊤ → HOK k T U H → ∀ R : Subgroup G,
      R0 k p T U H R → MaxIn {R' : Subgroup G | R0 k p T U (H ⊓ normalizer (R : Set G)) R'} R →
        MaxIn {R' : Subgroup G | R0 k p T U H R'} R

@[expose] def Prop10_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g →
      (∀ R : Subgroup G, Rp z k p T U Q M R → normalizer ((kInfty R : Subgroup G) : Set G) ≤ M) ∨ (p = 3 ∧ k = Kind.ly)

@[expose] def Prop10_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → ∀ N R : Subgroup G, IsCoatom N → Rp z k p T U Q M R → R ≤ N → T ≤ N →
      R0 k p T U N R → Fs N = Op p N → ¬ Q ⊓ R ≤ Cen z → N = M ∨ (p = 3 ∧ k = Kind.ly)

@[expose] def Prop11_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → ¬ T ≤ centralizer (U : Set G)

@[expose] def Prop11_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → TypeOneCase G k →
      (∃ R : Subgroup G, Rp z k p T U Q M R ∧
        Covers (normalizer (R : Set G)) (normalizer (U : Set G)) (centralizer (U : Set G)) ∧
        ¬ normalizer (R : Set G) ≤ M) ∧ p = 3 ∧ k = Kind.ly

end CFSG.GH74.GLS.Stage2.Bender.Thm2
