module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QShp
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint

theorem famF_trialityD4 :
    FamF .trialityD4 := by
  refine famF_of_fAt fun X _ _ _ n p f hp hp2 hX hq z hz => ?_
  have hn : n = 0 := by
    rcases hX with ⟨ht, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact absurd ht (by simp [classicalTags])
    all_goals exact h0
  subst hn
  obtain ⟨F₁, F₂, _, _, _, _, S, hc₁, hc₂, hSz⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hX z hz
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h1 : 1 < Nat.card F₂ := Finite.one_lt_card
  have h₂ : 4 ≤ Nat.card F₂ := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have h₁ : 4 ≤ Nat.card F₁ := by
    rw [hc₁]
    calc 4 ≤ Nat.card F₂ := h₂
      _ = p ^ f := hc₂
      _ ≤ (p ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
  exact fAt_of_shape hz S hSz h₁ h₂

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
