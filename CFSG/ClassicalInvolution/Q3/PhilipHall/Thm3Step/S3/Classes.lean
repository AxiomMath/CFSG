module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Sub

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {K : Subgroup Y}

theorem thm3RConclG_twinOrbit (hΦ : TypeRHyp Φ) (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hin : InnerIH Y Φ) (htw : ¬ TwinOrbits Φ K) (g : Y) :
    Thm3RConclG (twinOrbit Φ K) (conjSub g K) := by
  obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 K hK).1
  have hKΔ : K ∈ twinOrbit Φ K := mem_twinOrbit_self hK hz
  exact hin _ (ncard_twinOrbit_lt hΦ.hyp.conjInvariant htw)
    (typeRHyp_of_subset hΦ (twinOrbit_subset hΦ.hyp.conjInvariant) twinOrbit_conjInvariant)
    _ (twinOrbit_conjInvariant g K hKΔ) (not_aEmpty_twinOrbit hΦ.hyp hK hA g)

theorem le_normalizer_of_not_mem_aStar {Δ : Set (Subgroup Y)} {K' : Subgroup Y}
    (hC : Thm3RConclG Δ K') {M M' : Subgroup Y} (hM' : M' ∈ Δ) (hM'n : M' ∉ aStar Δ K')
    (hM : M ∈ aStar Δ K') :
    M' ≤ Subgroup.normalizer (M : Set Y) ∧ M ≤ Subgroup.normalizer (M' : Set Y) := by
  obtain ⟨⟨heq, hcomm⟩, -⟩ := hC
  rw [heq] at hM'n hM
  have h := hcomm M' hM' hM'n M hM
  refine ⟨le_normalizer_of_commutator_le_oddCoreOf (h.trans inf_le_right),
    le_normalizer_of_commutator_le_oddCoreOf ?_⟩
  rw [Subgroup.commutator_comm]
  exact h.trans inf_le_left

theorem le_normalizer_omegaGen_aStar (hΦ : TypeRHyp Φ) (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hin : InnerIH Y Φ) (htw : ¬ TwinOrbits Φ K) :
    omegaGen (twinOrbit Φ K) ≤ Subgroup.normalizer (omegaGen (aStar Φ K) : Set Y) := by
  obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 K hK).1
  have hKΔ : K ∈ twinOrbit Φ K := mem_twinOrbit_self hK hz
  have hC := thm3RConclG_twinOrbit hΦ hK hA hin htw 1
  rw [conjSub_one] at hC
  have hst : aStar (twinOrbit Φ K) K = aStar Φ K := aStar_twinOrbit hΦ.hyp hKΔ
  refine iSup₂_le fun M hM => ?_
  by_cases hMC : M ∈ aStar Φ K
  · exact (T3Core.le_conjStab_aStar hΦ.hyp.conjInvariant hK hMC).trans
      (T3Core.conjStab_le_normalizer_omegaGen _)
  · refine le_normalizer_omegaGen fun N hN => ?_
    rw [← hst] at hMC hN
    exact (le_normalizer_of_not_mem_aStar hC hM hMC hN).1

theorem isSubnormal_omegaGen_aStar (hΦ : TypeRHyp Φ) (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hin : InnerIH Y Φ) (htw : ¬ TwinOrbits Φ K) : IsSubnormal (omegaGen (aStar Φ K)) ⊤ := by
  obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 K hK).1
  have hKΔ : K ∈ twinOrbit Φ K := mem_twinOrbit_self hK hz
  have hPX : omegaGen (aStar Φ K) ≤ omegaGen (twinOrbit Φ K) :=
    iSup₂_le fun M hM => le_omegaGen (aStar_subset_twinOrbit hΦ.hyp hKΔ hM)
  have hXn : (omegaGen (twinOrbit Φ K)).Normal := omegaGen_normal twinOrbit_conjInvariant
  exact IsSubnormal.step hPX ((Subgroup.normal_subgroupOf_iff_le_normalizer hPX).mpr
      (le_normalizer_omegaGen_aStar hΦ hK hA hin htw))
    (isSubnormal_of_normal_subgroupOf le_top inferInstance)

theorem oddCore_omegaGen_aStar_eq_bot (hΦ : TypeRHyp Φ) (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hin : InnerIH Y Φ) (htw : ¬ TwinOrbits Φ K) (hO : classicalInvolutionOddCore Y = ⊥) :
    classicalInvolutionOddCore ↥(omegaGen (aStar Φ K)) = ⊥ :=
  CFSG.ComponentClassification.OddCore.subnormal_corefree hO _
    (isSubnormal_omegaGen_aStar hΦ hK hA hin htw)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3
