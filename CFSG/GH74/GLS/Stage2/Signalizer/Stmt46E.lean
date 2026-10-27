module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Lemma4_6E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H X : Subgroup G) (p : ℕ), Sig4Sub G z H p X → ⁅Em H, X⁆ ≠ ⊥ →
      ∀ E : Subgroup G, E ≤ H ⊓ centralizer (X : Set G) →
        (E.subgroupOf (H ⊓ centralizer (X : Set G))).Normal → z ∈ normalizer (E : Set G) →
        Odd (Nat.card ↥E) → ¬ p ∣ Nat.card ↥E → E ≤ centralizer ((⁅Em H, X⁆ : Subgroup G) : Set G)

end CFSG.GH74.GLS.Stage2.Signalizer
