module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs
public import CFSG.LieType.Steinberg.CentralExt.Model

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Blueprint

theorem almostSimpleRestricted_oddLinearUnrestricted :
    RestrictedStd.AlmostSimpleRestricted RestrictedStd.OddLinearUnrestricted := by
  intro A _ _ W _ hWs hWnab hCW _ hP a ha L hLW _ hL hstd hs
  exfalso
  obtain ⟨n, ℓ, e, hℓ, hℓ2, he, hn, hm⟩ := hP
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := LieType.Steinberg.statedClassicalModel_of_lieModel
    (by decide) hm
  set φ' : W ≃* projectiveSL n K :=
    φ.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)) with hφ'
  have hn4 : 4 ≤ n := by omega
  rcases hs with ⟨p, f, -, hp2, -, -, hpm, hZ⟩ | ⟨h7, hZ⟩ | h34
  · obtain ⟨-, -, -, -, hm4, -⟩ := faithful_odd_higher_linear_socle_selector_core hWs hWnab hCW ha
      hLW hL hstd hp2 (Or.inl (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hpm))
      (fun _ => Or.inr hZ) hn4 hℓ hℓ2 he hK φ'
    omega
  · obtain ⟨-, -, -, -, hm4, -⟩ := faithful_odd_higher_linear_socle_selector_core
      (p := 3) (f := 1) hWs hWnab hCW ha hLW hL hstd (by decide) (Or.inr (Or.inl h7))
      (fun _ => Or.inr hZ) hn4 hℓ hℓ2 he hK φ'
    omega
  · have h34' := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h34
    obtain ⟨-, -, -, -, hm4, -⟩ := faithful_odd_higher_linear_socle_selector_core
      (p := 3) (f := 1) hWs hWnab hCW ha hLW hL hstd (by decide) (Or.inr (Or.inr h34'))
      (fun h => absurd h34'
        (UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated
          h).2.2)
      hn4 hℓ hℓ2 he hK φ'
    omega

end CFSG.ComponentClassification.OddSelector
