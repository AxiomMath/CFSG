module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeIndexTwo

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddLie

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddLieType_cases {F : Type} [Group F] (h : OddLieType F) :
    (∃ (t : StatedLieTag) (n p f : ℕ), p ≠ 2 ∧ StatedClassicalModel F t n p f) ∨
    (∃ p f : ℕ, ReeTitsModel F .twistedG2 p f) ∨
    ∃ (t : StatedLieTag) (p f : ℕ), t ∈ chevalleyExceptionalTags ∧ p.Prime ∧ p ≠ 2 ∧
      ChevalleyExceptionalModel F t p f := by
  obtain ⟨t, n, p, f, hp, hp2, -, hmodel⟩ := h
  rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hree⟩ | ⟨-, -, hsz⟩
  · exact Or.inl ⟨t, n, p, f, hp2, hcl⟩
  · exact Or.inr (Or.inr ⟨t, p, f, ht, hp, hp2, hex⟩)
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨p, f, hree⟩)
    · obtain ⟨⟨-, -, -, hp2', -⟩, -⟩ := hree
      exact absurd hp2' hp2
    · obtain ⟨⟨-, -, -, hp2', -⟩, -⟩ := hree
      exact absurd hp2' hp2
  · exact absurd hsz.1 hp2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem odd_Lie_index_two_B_of_exceptional
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (hodd : OddLieType (GeneralizedFitting.subgroup G))
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (hexc : ∀ (t : StatedLieTag) (p f : ℕ), t ∈ chevalleyExceptionalTags → p.Prime → p ≠ 2 →
      ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) t p f →
      CentralTwoBInclusion.Property G) :
    CentralTwoBInclusion.Property G := by
  rcases oddLieType_cases hodd with ⟨t, n, p, f, hp2, hcl⟩ | ⟨p, f, hree⟩ |
      ⟨t, p, f, ht, hp, hp2, hex⟩
  · exact (odd_classical_index_two_B_under_proper_subgroup_B hnonab hindex t n p f hp2 hcl
      hproper).2
  · exact (CatalogueBSmallRee.small_Ree_index_two_B_under_proper_subgroup_B hnonab hindex p f
      hree hproper).2
  · exact hexc t p f ht hp hp2 hex

end CFSG.ComponentClassification.CatalogueBOddLie
