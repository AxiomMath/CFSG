module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I113UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (K : Subgroup G), GLAIsBmax p B → IsEssential p B x →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K →
    ¬ B ≤ Subgroup.normalizer (K : Set G) →
    ∃ A : Subgroup G, GLAIsBmax p A ∧ B ⊓ centModSubgroup p K ≤ A ∧
      (∀ b ∈ B, A ≤ Subgroup.normalizer (GLBConj b K : Set G)) ∧
      (∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ closureIn K B, a = u * v) ∧
      ¬ IsCyclic (A ⊓ closureIn K B ⊓ centModSubgroup p K : Subgroup G)

end CFSG.LocalAnalysis.GLTheoremA
