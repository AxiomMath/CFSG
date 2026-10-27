module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_exists_choice {M N J U : Subgroup G}
    (h : ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M ∧
      invariantTwoMaximalWithin U J (S₁ ⊓ J)) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M ∧
      invariantTwoMaximalWithin U J (S₁ ⊓ J) ∧
      ∀ S₁' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁' → ¬ S₁' ≤ M →
        invariantTwoMaximalWithin U J (S₁' ⊓ J) →
        Nat.card (S₁' ⊓ M : Subgroup G) < Nat.card (S₁ ⊓ M : Subgroup G) ∨
          (Nat.card (S₁' ⊓ M : Subgroup G) = Nat.card (S₁ ⊓ M : Subgroup G) ∧
            Nat.card (S₁' ⊓ N : Subgroup G) ≤ Nat.card (S₁ ⊓ N : Subgroup G)) := by
  set s : Set (Subgroup G) := {S₁ | rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M ∧
    invariantTwoMaximalWithin U J (S₁ ⊓ J)} with hs
  obtain ⟨S₀, hS₀⟩ := h
  obtain ⟨S₁, hS₁, hmax⟩ := Set.exists_max_image s
    (fun S : Subgroup G => toLex (Nat.card (S ⊓ M : Subgroup G), Nat.card (S ⊓ N : Subgroup G)))
    (Set.toFinite s) ⟨S₀, hS₀⟩
  refine ⟨S₁, hS₁.1, hS₁.2.1, hS₁.2.2, fun S₁' h1 h2 h3 => ?_⟩
  have h := hmax S₁' ⟨h1, h2, h3⟩
  rw [Prod.Lex.le_iff] at h
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, h'⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
