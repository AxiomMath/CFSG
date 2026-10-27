module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

@[expose] def BinaryActionRankAlternatives (G : Type) [Group G] [Finite G] (p : ℕ) (P B : Subgroup G) (e : ℕ)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) : Prop :=
  e + 1 < moduleM ρ ∨
    (∃ q ∈ piOf B ∩ alphaSet G, ∃ Q ∈ scriptQ G q, 3 < CFSG.Open.pRank q Q) ∨
    (P ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ ∧ 3 < CFSG.Open.pRank p P ∧
      ¬ ∃ x : G, ∀ b ∈ B, x * b * x⁻¹ = b⁻¹)

structure BinaryActionRankCounterexample (G : Type) [Group G] [Finite G] (p : ℕ) (P T B : Subgroup G) (e : ℕ)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) :
    Prop where
  oddPrimeClassTwoAction : OddPrimeClassTwoAction G p P T B e
  faithfulBinaryIrreducibleAction : FaithfulBinaryIrreducibleAction G p P T B ρ
  cyclicCentralizersAndFewComponentConjugates : CyclicCentralizersAndFewComponentConjugates G B
  not_concl : ¬ BinaryActionRankAlternatives G p P B e ρ

end Section5

end CFSG.LocalAnalysis.RankThreeUC
