module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter
import CFSG.FeitThompson.Local.PuigTermsContainAbelianNormal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {X : Type*} [Group X]

theorem center_le_puigCenter : center X ≤ puigCenter X := by
  rw [puigCenter_eq_inf_centralizer]
  refine le_inf (le_puigSubgroup_of_normal inferInstance) fun x hx => ?_
  exact mem_centralizer_iff.2 fun g _ => mem_center_iff.1 hx g

theorem puigCenter_ne_bot_of_center_ne_bot (h : center X ≠ ⊥) : puigCenter X ≠ ⊥ := fun hb =>
  h (le_bot_iff.1 (hb ▸ center_le_puigCenter))

variable {p : ℕ} {P : Type*} [Group P]

theorem puigCenter_ne_bot [Finite P] [Nontrivial P] (hp : p.Prime) (hP : IsPGroup p P) :
    puigCenter P ≠ ⊥ := by
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  refine puigCenter_ne_bot_of_center_ne_bot (center_ne_bot hp ha ?_)
  rcases Nat.eq_zero_or_pos a with rfl | h
  · rw [pow_zero] at ha
    exact absurd ha Finite.one_lt_card.ne'
  · exact h

theorem puigCenter_nontrivial [Finite P] [Nontrivial P] (hp : p.Prime) (hP : IsPGroup p P) :
    Nontrivial (puigCenter P) :=
  (Subgroup.nontrivial_iff_ne_bot _).2 (puigCenter_ne_bot hp hP)

theorem puigCenter_ne_bot_and_characteristic [Finite P] [Nontrivial P] (hp : p.Prime)
    (hP : IsPGroup p P) : puigCenter P ≠ ⊥ ∧ (puigCenter P).Characteristic :=
  ⟨puigCenter_ne_bot hp hP, puigCenter_characteristic⟩

end CFSG.FeitThompson

end
