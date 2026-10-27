module

public import CFSG.GH74.E2.Q8CaseI
public import CFSG.GH74.E2.Q8CaseII
public import CFSG.GH74.E2.Q8Iso
public import CFSG.GH74.E2.Shapes

public section

namespace CFSG.GH74.E2

open Subgroup

namespace Q8

theorem card_eq_eight :
    ∀ (n : ℕ) (X : Type) [Group X] [Finite X] (c : MulAut X), Nat.card X = n → Good X c →
      (∃ t : X, t ≠ 1 ∧ c t = t) → Nat.card X = 8 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ c hn hg hfix
    by_cases htriv : ∀ p ∈ frattini X, c p = p
    · exact (caseI hg hfix htriv).1
    · exfalso
      push Not at htriv
      refine caseII hg hfix htriv ?_
      intro Y _ _ d hlt hgd hfixd
      exact ih (Nat.card Y) (hn ▸ hlt) Y d rfl hgd hfixd

end Q8

theorem q8Lemma : Q8Lemma := by
  intro X _ _ c hX hrank hsub hord hfpf hfix
  have hg : Q8.Good X c := ⟨hX, hrank, hsub, by rw [← hord]; exact pow_orderOf_eq_one c, hfpf⟩
  by_cases htriv : ∀ p ∈ frattini X, c p = p
  · obtain ⟨hcard, x, y, -, hx1, hx4, hyy, hxy⟩ := Q8.caseI hg hfix htriv
    exact (Q8.quaternion_iso hcard hx1 hx4 hyy hxy).map MulEquiv.symm
  · exfalso
    push Not at htriv
    refine Q8.caseII hg hfix htriv ?_
    intro Y _ _ d hlt hgd hfixd
    exact Q8.card_eq_eight (Nat.card Y) Y d rfl hgd hfixd

end CFSG.GH74.E2
