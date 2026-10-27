module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

@[expose] def centerP (P : Subgroup G) : Subgroup G := (Subgroup.center ↥P).map P.subtype

@[expose] def ExtraspecialBinaryActionAlternatives (G : Type) [Group G] [Finite G] (p : ℕ) (P B : Subgroup G) (e : ℕ)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) : Prop :=
  (∃ k : ℕ, e = 2 ^ k) ∧
    ((p ∈ piOf B ∧ 3 < CFSG.Open.pRank p P) ∨
      (IsCyclic ↥B ∧
        (∀ b ∈ B, b ≠ 1 → P ⊓ Subgroup.centralizer ({b} : Set G) = centerP P) ∧
        e + 1 < moduleM ρ))

structure ExtraspecialBinaryActionCounterexample (G : Type) [Group G] [Finite G] (p : ℕ) (P T B : Subgroup G) (e : ℕ)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) :
    Prop where
  oddPrimeClassTwoAction : OddPrimeClassTwoAction G p P T B e
  faithfulBinaryIrreducibleAction : FaithfulBinaryIrreducibleAction G p P T B ρ
  extraspecial : CFSG.IsExtraspecialPGroup p ↥P
  not_concl : ¬ ExtraspecialBinaryActionAlternatives G p P B e ρ

end Section5

end CFSG.LocalAnalysis.RankThreeUC
