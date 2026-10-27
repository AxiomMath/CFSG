module

public import CFSG.ClassicalInvolution.Q3.Q3Y2WireU
public import CFSG.ClassicalInvolution.Q3.Q3Y2Comp
public import CFSG.ClassicalInvolution.Q3.Q3Y2Lift
public import CFSG.ClassicalInvolution.Q3.Q3YLink
public import CFSG.ClassicalInvolution.Q3.Q3CAlpha
public import CFSG.ClassicalInvolution.ModelFacts.TG3Final

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y2

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts

theorem modelTwinGen3_of_noExc (hExc : TG3.TwinNoExc3) : ModelTwinGen3 := by
  intro t n hfund hadm hG2 hD4
  cases t with
  | PSL =>
    by_cases hk : n = 4
    · subst hk
      exact twinStrong3_psl_four
    · exact twinStrong3_psl_ne_four hadm hk
  | PSU =>
    by_cases hk : n = 4
    · subst hk
      exact twinStrong3_psu_four hadm
    · exact twinStrong3_psu_ne_four hadm hk
  | PSp => exact twinStrong3_psp hadm
  | POmegaOdd => exact twinStrong3_pOmegaOdd hadm
  | POmegaMinus => exact twinStrong3_pOmegaMinus hadm
  | POmegaPlus =>
    by_cases hk : n = 4
    · subst hk
      exact twinStrong3_pOmegaPlus_four hadm
    · exact twinStrong3_pOmegaPlus hadm (by have := hadm.2.2; omega)
  | F4 =>
    intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _
    exact absurd hcen (hExc .F4 n (Or.inl rfl) hadm R₁ hR₁ R₂ hR₂ hne e₁ e₂)
  | E6 =>
    intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _
    exact absurd hcen (hExc .E6 n (Or.inr (Or.inl rfl)) hadm R₁ hR₁ R₂ hR₂ hne e₁ e₂)
  | E7 =>
    intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _
    exact absurd hcen
      (hExc .E7 n (Or.inr (Or.inr (Or.inl rfl))) hadm R₁ hR₁ R₂ hR₂ hne e₁ e₂)
  | E8 =>
    intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _
    exact absurd hcen
      (hExc .E8 n (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm R₁ hR₁ R₂ hR₂ hne e₁ e₂)
  | twistedE6 =>
    intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _
    exact absurd hcen
      (hExc .twistedE6 n (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm R₁ hR₁ R₂ hR₂ hne e₁ e₂)
  | G2 => exact absurd rfl hG2
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 => exact hfund.elim
  | twistedG2 => exact hfund.elim
  | twistedF4 => exact hfund.elim
  | Tits => exact hfund.elim

end CFSG.ClassicalInvolution.Q3.Q3Y2
