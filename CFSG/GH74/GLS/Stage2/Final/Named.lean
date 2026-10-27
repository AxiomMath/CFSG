module

public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def ExistsEvenFStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∃ M ∈ maximalOverCentralizer z, Even (Nat.card ↥(generalizedFitting ↥M))

structure Stage2Out (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) : Prop where
  oddCore : (∀ ε : Bool, k ≠ Kind.l4 ε) → pPrimeCore 2 ↥(Cen z) = ⊥
  oddCoreL4 : ∀ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), k = Kind.l4 ε →
    Stage1L4 G z S ε q L₁ L₂ → IsCyclic ↥(pPrimeCore 2 ↥(Cen z)) ∧
      Nat.card ↥(pPrimeCore 2 ↥(Cen z)) ∣ (if ε then q - 1 else q + 1)
  sixA : ∀ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), k = Kind.l4 ε →
    Stage1L4 G z S ε q L₁ L₂ → ∀ p f : ℕ, p.Prime → p ^ f = q →
      ∀ M : Subgroup G, IsCoatom M → Cen z < M →
        IsCoatom ((Cen z).subgroupOf M) ∧ LieModel ↥(generalizedFitting ↥M) .PSp 2 p f

@[expose] def Stage2Main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    Stage2Out G z k S

end CFSG.GH74.GLS.Stage2.Final
