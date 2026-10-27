module


public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

def piOf (B : Subgroup G) : Set ℕ := {r | r.Prime ∧ r ∣ Nat.card B}

@[expose] noncomputable def binaryMultiplicativeOrder (q : ℕ) : ℕ := orderOf (2 : ZMod q)

structure Setting (G : Type) [Group G] [Finite G] (p : ℕ) (P T B : Subgroup G) : Prop where
  prime : p.Prime
  odd : Odd p
  pGroup : IsPGroup p P
  exponent : Monoid.exponent P = p
  class_le_two : ⁅⁅P, P⁆, P⁆ = ⊥
  twoGroup : IsPGroup 2 T
  abelian : IsMulCommutative B
  oddOrder : Odd (Nat.card B)
  prod_comm : (T : Set G) * (B : Set G) = (B : Set G) * (T : Set G)
  normT : T ≤ Subgroup.normalizer (P : Set G)
  normB : B ≤ Subgroup.normalizer (P : Set G)

structure OddPrimeClassTwoAction (G : Type) [Group G] [Finite G] (p : ℕ) (P T B : Subgroup G) (e : ℕ) : Prop where
  setting : Setting G p P T B
  cyclic_centralizer : ∀ b ∈ B, b ≠ 1 → IsCyclic ↥(P ⊓ Subgroup.centralizer ({b} : Set G))
  two_lt : 2 < e
  pi_eq : piOf B = {r | r.Prime ∧ r ∣ 2 ^ e - 1}
  exponent_Or : ∀ r ∈ piOf B, Monoid.exponent ↥(CFSG.Open.pCoreOf r B) = r
  normalizes : Odd e → B ≤ Subgroup.normalizer (T : Set G)

@[expose] def twoCoreCommutator (T B : Subgroup G) : Subgroup G := ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), B⁆

noncomputable def sylowFixedSubmodule {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (T : Subgroup G) : Submodule (ZMod 2) V :=
  fixedSubmodule ρ T

structure FaithfulBinaryIrreducibleAction (G : Type) [Group G] [Finite G] (p : ℕ) (P T B : Subgroup G)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) :
    Prop where
  faithful : Function.Injective ρ
  irreducible : ρ.IsIrreducible
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  comm_Z_B : ∀ z ∈ sylowFixedSubmodule ρ T, ∀ b ∈ B, ρ b z = z
  normal : P.Normal
  rank_gt : 1 < CFSG.Open.pRank p P
  minimal : ∀ Q : Subgroup G, Q.Normal → 1 < CFSG.Open.pRank p Q → Q ≤ P → Q = P

def alphaSet (G : Type) [Group G] [Finite G] : Set ℕ :=
  {q | q.Prime ∧ 1 < CFSG.Open.pRank q (CFSG.Open.pCoreOf q (commutator G))}

def scriptQ (G : Type) [Group G] [Finite G] (q : ℕ) : Set (Subgroup G) :=
  {Q | Q.Normal ∧ IsPGroup q Q ∧ ¬ IsCyclic Q ∧ Monoid.exponent Q = q ∧ ⁅⁅Q, Q⁆, Q⁆ = ⊥ ∧
    Q ≤ commutator G}

structure CyclicCentralizersAndFewComponentConjugates (G : Type) [Group G] [Finite G] (B : Subgroup G) : Prop where
  cyclic_centralizer : ∀ q ∈ alphaSet G, ∀ Q ∈ scriptQ G q, ∀ b ∈ B, b ≠ 1 →
    IsCyclic ↥(Q ⊓ Subgroup.centralizer ({b} : Set G))
  few_conjugates : ∀ L : Subgroup G, CFSG.Open.IsComponentOf L ⊤ →
    {L' : Subgroup G | ∃ g : G, L' = L.map (MulAut.conj g).toMonoidHom}.ncard ≤ 2

@[expose] def Delta {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (p : ℕ) (P : Subgroup G)
    (ρ : Representation (ZMod 2) G V) : Set (Subgroup G) :=
  {D | D ≤ P ∧ D.relIndex P = p ∧ fixedSubmodule ρ D ≠ ⊥}

theorem mem_Delta_iff {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (p : ℕ) (P : Subgroup G)
    (ρ : Representation (ZMod 2) G V) (D : Subgroup G) :
    D ∈ Delta p P ρ ↔ D ≤ P ∧ D.relIndex P = p ∧ fixedSubmodule ρ D ≠ ⊥ := Iff.rfl

theorem binaryMultiplicativeOrder_eq_orderOf (q : ℕ) : binaryMultiplicativeOrder q = orderOf (2 : ZMod q) := rfl

end Section5

end CFSG.LocalAnalysis.RankThreeUC
