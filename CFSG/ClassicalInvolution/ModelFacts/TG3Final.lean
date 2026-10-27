module

public import CFSG.ClassicalInvolution.ModelFacts.TG3D4
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSL
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSU
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSp
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSL
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSU
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSp
public import CFSG.ClassicalInvolution.Uniform.U5Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Residuals

@[expose] def TwinNoExc3 : Prop :=
  ∀ (t : StatedLieTag) (k : ℕ), (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    StatedLieAdmissible t k 3 1 →
    ∀ R₁ ∈ fundamentalSubgroups t (modelUniv t k 3 1 Fact.out).D,
    ∀ R₂ ∈ fundamentalSubgroups t (modelUniv t k 3 1 Fact.out).D, R₁ ≠ R₂ →
    ∀ (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃)),
      sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center (modelUniv t k 3 1 Fact.out).K

end Residuals

section Main


theorem compGen3Twin_exc (hExc : TwinNoExc3) {t : StatedLieTag} {k : ℕ}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hadm : StatedLieAdmissible t k 3 1) : CompGen3Twin (compModel 3 1 t k) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag t := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> trivial
  have hG2 : t ≠ .G2 := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide
  have hfin : Finite (compModel 3 1 t k).G :=
    finite_modelUniv hp2 Nat.prime_three hfund hadm
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hcomm z hz₁ hz₂ A hA hAle hzA
  exfalso
  obtain ⟨e₁⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4 hR₁
  obtain ⟨e₂⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4 hR₂
  exact hExc t k ht hadm R₁ hR₁ R₂ hR₂ (fun h => hne (by rw [h])) e₁ e₂
    (hker (twin_ratio_mem_ker ψ e₁ e₂ h24₁ h24₂ hz₁ hz₂))

theorem twinGen3_of (hExc : TwinNoExc3) : TwinGen3 := by
  intro t k hfund hadm hG2 hD4
  cases t with
  | PSL =>
    by_cases hk : k = 4
    · subst hk
      exact compGen3Twin_psl_four hadm
    · exact compGen3Twin_psl hadm hk
  | PSU =>
    by_cases hk : k = 4
    · subst hk
      exact compGen3Twin_psu_four hadm
    · exact compGen3Twin_psu hadm hk
  | PSp =>
    by_cases hk : k = 2
    · subst hk
      exact compGen3Twin_psp_two hadm
    · exact compGen3Twin_psp hadm hk
  | POmegaOdd => exact compGen3Twin_pOmegaOdd hadm
  | POmegaMinus => exact compGen3Twin_pOmegaMinus hadm
  | POmegaPlus =>
    by_cases hk : k = 4
    · subst hk
      exact compGen3Twin_pOmegaPlus_four hadm
    · exact compGen3Twin_pOmegaPlus hadm (by have := hadm.2.2; omega)
  | F4 => exact compGen3Twin_exc hExc (Or.inl rfl) hadm
  | E6 => exact compGen3Twin_exc hExc (Or.inr (Or.inl rfl)) hadm
  | E7 => exact compGen3Twin_exc hExc (Or.inr (Or.inr (Or.inl rfl))) hadm
  | E8 => exact compGen3Twin_exc hExc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm
  | twistedE6 => exact compGen3Twin_exc hExc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm
  | G2 => exact absurd rfl hG2
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 => exact hfund.elim
  | twistedG2 => exact hfund.elim
  | twistedF4 => exact hfund.elim
  | Tits => exact hfund.elim

end Main

end CFSG.ClassicalInvolution.ModelFacts.TG3
