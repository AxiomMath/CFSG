module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieTwistedE6

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddLie

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem exceptional_index_two_B_of_odd
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) (t : StatedLieTag)
    (p f : ℕ) (ht : t ∈ chevalleyExceptionalTags) (hp2 : p ≠ 2)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) t p f) :
    CentralTwoBInclusion.Property G := by
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .G2 (Or.inl rfl) p f
      hp2 hmodel hproper).2
  · exact (odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .F4
      (Or.inr (Or.inl rfl)) p f hp2 hmodel hproper).2
  · exact odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex .E6 p f (Or.inl rfl) hp2 hmodel
      hproper
  · exact odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex .E7 p f (Or.inr (Or.inl rfl))
      hp2 hmodel hproper
  · exact (odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .E8
      (Or.inr (Or.inr rfl)) p f hp2 hmodel hproper).2
  · exact odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex .twistedE6 p f
      (Or.inr (Or.inr (Or.inl rfl))) hp2 hmodel hproper
  · exact odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex .trialityD4 p f
      (Or.inr (Or.inr (Or.inr rfl))) hp2 hmodel hproper

theorem odd_Lie_outside_classical_small_Ree_B_frontier
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (hodd : OddLieType (GeneralizedFitting.subgroup G))
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (hPSL : ∀ n p f : ℕ, 2 ≤ n → p.Prime → p ≠ 2 → 1 ≤ f →
      ¬ StatedClassicalModel (GeneralizedFitting.subgroup G) .PSL n p f)
    (hPSU : ∀ n p f : ℕ, 3 ≤ n → p.Prime → p ≠ 2 → 1 ≤ f →
      ¬ StatedClassicalModel (GeneralizedFitting.subgroup G) .PSU n p f)
    (hPSp : ∀ n p f : ℕ, 2 ≤ n → p.Prime → p ≠ 2 → 1 ≤ f →
      ¬ StatedClassicalModel (GeneralizedFitting.subgroup G) .PSp n p f)
    (hPOmega : ∀ (t : StatedLieTag) (n p f : ℕ),
      (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → p.Prime → p ≠ 2 → 1 ≤ f →
        ¬ StatedClassicalModel (GeneralizedFitting.subgroup G) t n p f)
    (hRee : ∀ p f : ℕ, ¬ ReeTitsModel (GeneralizedFitting.subgroup G) .twistedG2 p f) :
    CentralTwoBInclusion.Property G := by
  rcases oddLieType_cases hodd with ⟨t, n, p, f, hp2, hcl⟩ | ⟨p, f, hree⟩ |
      ⟨t, p, f, ht, -, hp2, hex⟩
  · exfalso
    obtain ⟨hp, hf, -⟩ := hcl.1
    cases t
    case PSL => exact hPSL n p f hcl.1.2.2.1 hp hp2 hf hcl
    case PSU => exact hPSU n p f hcl.1.2.2.1 hp hp2 hf hcl
    case PSp => exact hPSp n p f hcl.1.2.2.1 hp hp2 hf hcl
    case POmegaOdd => exact hPOmega _ n p f (Or.inl rfl) hp hp2 hf hcl
    case POmegaPlus => exact hPOmega _ n p f (Or.inr (Or.inl rfl)) hp hp2 hf hcl
    case POmegaMinus => exact hPOmega _ n p f (Or.inr (Or.inr rfl)) hp hp2 hf hcl
    all_goals exact hcl.2.elim
  · exact absurd hree (hRee p f)
  · exact exceptional_index_two_B_of_odd hnonab hindex hproper t p f ht hp2 hex

theorem odd_Lie_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (hodd : OddLieType (GeneralizedFitting.subgroup G))
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    CentralTwoBInclusion.Property G :=
  odd_Lie_index_two_B_of_exceptional hnonab hindex hodd hproper fun t p f ht _ hp2 hex =>
    exceptional_index_two_B_of_odd hnonab hindex hproper t p f ht hp2 hex

end CFSG.ComponentClassification.CatalogueBOddLie
