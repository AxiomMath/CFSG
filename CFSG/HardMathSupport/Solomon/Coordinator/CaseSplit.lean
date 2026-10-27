module

public import CFSG.HardMathSupport.Solomon.Coordinator.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem existsPreUniquenessSubgroup_of_props (h41 : Prop41) (h42 : Prop42)
    (h4 : CaseFourPreUniqueness) : ExistsPreUniquenessSubgroup := by
  intro G _ _ m p hS
  rcases (h41 G m p hS).2 with h | h | h | h
  · exact h42 G m p hS (Or.inl h)
  · exact h42 G m p hS (Or.inr (Or.inl h))
  · exact h42 G m p hS (Or.inr (Or.inr h))
  · exact h4 G m p hS h

theorem theoremOne_of_props (h41 : Prop41) (h42 : Prop42) (h4 : CaseFourPreUniqueness)
    (h81 : Prop81Core) : TheoremOne :=
  theoremOne_of_prop81Core (existsPreUniquenessSubgroup_of_props h41 h42 h4) h81

theorem cases_of_caseOne_of_five_lt {G : Type} [Group G] [Finite G] {m p : ℕ}
    (hS : GLStanding G m p) (h : 5 < p → GLCaseOne G p) :
    GLCaseOne G p ∨ GLCaseTwo G p ∨ GLCaseThree G p ∨ GLCaseFour G p := by
  by_cases h1 : GLCaseOne G p
  · exact Or.inl h1
  have hp5 : p ≤ 5 := by
    by_contra h5
    exact h1 (h (by omega))
  have hp := hS.prime
  have hp2 := hS.ne_two
  have hr := hS.rank_eq
  have hm := hS.four_le
  have hp35 : p = 3 ∨ p = 5 := by
    have h2 := hp.two_le
    interval_cases p
    · exact absurd rfl hp2
    · exact Or.inl rfl
    · exact absurd hp (by decide)
    · exact Or.inr rfl
  by_cases hm5 : 5 ≤ m
  · exact Or.inr (Or.inl ⟨hp5, hr ▸ hm5, h1⟩)
  · have hm4 : m = 4 := by omega
    rcases hp35 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, hr.trans hm4, h1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hr.trans hm4, h1⟩))

end CFSG.HardMathSupport.Solomon.Coordinator
