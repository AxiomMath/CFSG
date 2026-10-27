module

public import CFSG.CGT.T75E.Reduce
public import CFSG.CGT.T75E.RootBender
public import CFSG.CGT.T75E.RootLin
public import CFSG.CGT.T75E.RootSmall
public import CFSG.CGT.Timmesfeld75.AschbacherNoPolarDischarge
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki

theorem rootGroup_of_asc (hAsc : AschbacherNoPolarInput)
    (h26 : Lemma26Simple) : Sec4I4RootGroupInput := by
  intro K _ _ _ Tb hyp Yb c₁ c₂ hY f hf hρ
  obtain ⟨ρ, hρ⟩ := hρ
  subst hY
  have hT : IsWC Tb := hyp.1
  have hT1 : Tb ≠ ⊥ := hyp_ne_bot hyp
  obtain ⟨hcases, -⟩ := h26 K Tb hyp
  rcases hcases with ⟨n, m, hn, hm, hG⟩ | ⟨m, hm, hG⟩ | ⟨s, hs, hs3, hG⟩ | ⟨e⟩
  · rcases hn.eq_or_lt with rfl | hn3
    · exact (rootGroup_l2 (Tb := Tb) (c₁ := c₁) (c₂ := c₂) hG hT hT1 hf ρ hρ).elim
    · exact (rootGroup_lin_of_model (Tb := Tb) (c₁ := c₁) (c₂ := c₂) hn3 hG hT hT1 hf ρ hρ).elim
  · exact rootGroup_u3 (Tb := Tb) (c₁ := c₁) (c₂ := c₂) hAsc hm hG hT hT1 hf ρ hρ
  · obtain ⟨a, -, -, ⟨e⟩⟩ := exists_sz_of_lieModel hG
    exact (rootGroup_sz (Tb := Tb) (c₁ := c₁) (c₂ := c₂) e hf ρ hρ).elim
  · exact (rootGroup_a6 (Tb := Tb) (c₁ := c₁) (c₂ := c₂) e.some hf ρ hρ).elim


theorem rootGroup_of_simple (h26 : Lemma26Simple) : Sec4I4RootGroupInput :=
  rootGroup_of_asc aschbacherNoPolarInput_of_repo h26

end CFSG.CGT.T75E
