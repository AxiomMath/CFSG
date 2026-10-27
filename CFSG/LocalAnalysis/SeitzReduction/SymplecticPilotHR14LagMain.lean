module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagC
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaStepOneOdd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.OrthogonalInvolutions (mem_omegaGroup)

theorem omegaLagrangianAO2Input_holds : OmegaLagrangianAO2Input := by
  intro F _ _ _ V _ _ _ Q hF hQ N _ hN4 _ s hsΩ hss hl hW
  exact mem_omegaO2Cent_of_typeA_four_dvd hF hQ (omega_le_orthogonalGroup hsΩ) hss hW
    (hl ▸ hN4)

theorem omegaLagrangianCO2Input_holds : OmegaLagrangianCO2Input := by
  intro F _ _ _ V _ _ _ Q _ hQ h8 s hsΩ hss hl hW
  have hev : Even (finrank F (omegaInvSpace s)) :=
    (mem_omegaGroup.1 (omega_le_omegaGroup hQ hsΩ)).2
  exact mem_omegaO2Cent_of_typeC_four_le hQ (omega_le_orthogonalGroup hsΩ) hss hW hev
    (by omega)

theorem spOmegaStepOneInput_of_aTwo {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    (hA2 : SpOmegaLagrangianATwoInput κ) : SpOmegaStepOneInput κ :=
  spOmegaStepOneInput_of_inputs hκ omegaLagrangianCO2Input_holds omegaLagrangianAO2Input_holds
    hA2

theorem mem_omegaO2Cent_of_mem_omega_of_not_aTwo {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) (h8 : 8 ≤ finrank K V)
    {s : V ≃ₗ[K] V}
    (hsΩ : s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hss : s * s = 1)
    (hnot : ¬ (2 * finrank K (omegaInvSpace s) = finrank K V ∧
      (∀ w ∈ omegaInvSpace s, Q w = 0) ∧ finrank K (omegaInvSpace s) % 4 = 2)) :
    s ∈ omegaO2Cent Q s := by
  have hs := omega_le_orthogonalGroup hsΩ
  have hle : 2 * finrank K (omegaInvSpace s) ≤ finrank K V :=
    CFSG.RankThree.OrthogonalInvolutions.two_mul_finrank_commSpace_le hss
  have hev : Even (finrank K (omegaInvSpace s)) :=
    (mem_omegaGroup.1 (omega_le_omegaGroup hQ hsΩ)).2
  rcases hle.lt_or_eq with hlt | heq
  · exact mem_omegaO2Cent_of_mem_omega hK hQ hsΩ hss hlt
  by_cases hW : ∀ w ∈ omegaInvSpace s, Q w = 0
  · refine mem_omegaO2Cent_of_typeA_four_dvd hK hQ hs hss hW ?_
    obtain ⟨j, hj⟩ := hev
    have h2 : finrank K (omegaInvSpace s) % 4 ≠ 2 := fun h2 => hnot ⟨heq, hW, h2⟩
    omega
  · push Not at hW
    exact mem_omegaO2Cent_of_typeC_four_le hQ hs hss hW hev (by omega)

end CFSG.SeitzReduction.SymplecticPilot
