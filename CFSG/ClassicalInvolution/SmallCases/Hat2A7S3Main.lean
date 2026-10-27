module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SStd
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S3Aux
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Main

variable {G : Type} [Group G] [Finite G]

theorem omegaStarNbr_subset_omegaNbr_a7 {Ω : Set (Subgroup G)} {K : Subgroup G}
    (hpre : Pre2A7 Ω K) {M J : Subgroup G} (hM : M ∈ Ω) (hJ : J ∈ Ω)
    (h : J ∈ omegaStarNbr Ω M) : J ∈ omegaNbr Ω M := by
  have hΩ : HypOmegaGen Ω := hpre.hyp
  obtain ⟨-, hJM, U, hU, hUJ, hUN⟩ := h
  obtain ⟨-, -, -, hU2, hcard⟩ := uset_data hpre.classical hU
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨hjU, huniq⟩ := involution_mem_of_card hj hUJ hcard
  obtain ⟨m, hm⟩ := hpre.classical M hM
  obtain ⟨R, hR, hRc⟩ := exists_sylow_centralized hm hUN hU2 hjU huniq (by omega) hj.sq
    hj.ne_one
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hM hR
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRset).exists_not_commute
  have hnc : ∃ a ∈ R, a ∉ Subgroup.centralizer (M : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hxy₀ ((Subgroup.mem_centralizer_iff.mp (hcon x₀ hx₀)) y₀ (hR.1 hy₀)).symm
  have hN5 : ∀ v ∈ R, v ∉ Subgroup.centralizer (M : Set G) →
      v ∈ Subgroup.normalizer (J : Set G) := by
    intro v hv hvc
    refine hΩ.omega5 J hJ M hM hJM j hj v (hR.1 hv) ?_ ?_ (hRc v hv).symm
    · intro hall
      exact hvc (Subgroup.mem_centralizer_iff.mpr fun w hw => (hall w hw).symm)
    · exact hR.2.1.to_le (Subgroup.zpowers_le.mpr hv)
  have hRN : R ≤ Subgroup.normalizer (J : Set G) := by
    intro v hv
    by_cases hvc : v ∈ Subgroup.centralizer (M : Set G)
    · obtain ⟨a, ha, hac⟩ := hnc
      have haN := hN5 a ha hac
      have hva : v * a ∉ Subgroup.centralizer (M : Set G) := by
        intro hva
        apply hac
        have h1 := (Subgroup.centralizer (M : Set G)).mul_mem
          ((Subgroup.centralizer (M : Set G)).inv_mem hvc) hva
        simpa using h1
      have hvaN := hN5 (v * a) (R.mul_mem hv ha) hva
      have h2 := (Subgroup.normalizer (J : Set G)).mul_mem hvaN
        ((Subgroup.normalizer (J : Set G)).inv_mem haN)
      simpa using h2
    · exact hN5 v hv hvc
  have hMJ : M ∈ omegaNbr Ω J := ⟨hM, Ne.symm hJM, R, hRset, hR.1, hRN⟩
  exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ hM hMJ

theorem pre2A7_aEmpty {Ω : Set (Subgroup G)} {K : Subgroup G} (hpre : Pre2A7 Ω K)
    {M : Subgroup G} (hM : M ∈ Ω) : AEmpty Ω M := by
  intro J hJstar hJnot
  exact absurd (omegaStarNbr_subset_omegaNbr_a7 hpre hM hJstar.1 hJstar) hJnot

theorem a7T3_proved : A7T3 := by
  intro G _ _ _ Ω K hpre ⟨J, hJ, hnot⟩
  exact hnot (pre2A7_aEmpty hpre hJ)

end Main

end CFSG.ClassicalInvolution.Hat2A7S
