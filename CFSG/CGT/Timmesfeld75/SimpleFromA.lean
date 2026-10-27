module

public import CFSG.CGT.Timmesfeld75.SimpleCase

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem simpleCaseListStmt_of_theoremA (hA : TheoremAStmt) : SimpleCaseListStmt := by
  intro G _ _ _ hnonab T hT h4
  obtain ⟨x, hxT, hx1⟩ : ∃ x ∈ T, x ≠ 1 := by
    rcases T.bot_or_exists_ne_one with hbot | h
    · rw [hbot, Subgroup.card_bot] at h4
      omega
    · exact h
  have heven : Even (Nat.card G) := by
    have hord : orderOf x = 2 := orderOf_eq_prime (hT.1.2 x hxT) hx1
    exact even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard x)
  have hTne : T ≠ ⊥ := fun h => hx1 (Subgroup.mem_bot.1 (h ▸ hxT))
  exact listGroup_of_thmAConclusion_simple hnonab heven (normalClosure_eq_top_of_simple hTne)
    (hA G T hT)

end CFSG.CGT.Timmesfeld75
