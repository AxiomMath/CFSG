module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

structure EtaFacts {G : Type} [Group G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W V : Subgroup G) : Prop where
  comm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  sup_eq : W = V ⊔ (W ⊓ sec19Y K z)
  supU : W = (W ⊓ K) ⊔ V
  disj : V ⊓ sec19Y K z = ⊥
  cyclic : IsCyclic ↥(W ⊓ sec19Y K z)
  card : Nat.card ↥(W ⊓ sec19Y K z) = Nat.card ↥V
  four : 4 ≤ Nat.card ↥V
  normalizes : (S : Subgroup G) ⊓ sec19Y K z ≤ Subgroup.normalizer (W : Set G)
  cent : W ⊓ sec19Y K z =
    W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)

variable (p f : ℕ) [Fact p.Prime]

@[expose] def EtaYForm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      EtaFacts K z S W V

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
