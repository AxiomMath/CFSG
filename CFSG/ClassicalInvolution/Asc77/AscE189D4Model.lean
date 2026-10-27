module

public import CFSG.ClassicalInvolution.Asc77.AscE189D4

public section

namespace CFSG.ClassicalInvolution.Asc77

section Spin8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem e189AtFam_spin_of_eight (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 8) (hZ : CenterScalar Q)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕) (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q) :
    E189AtFam (spinGroup Q) 𝓕 := by
  intro N hN F₁ hF₁ z₁ hz₁ g h1 _ h3 h4 _
  right
  rcases e189_commute_or_proj hodd hQ (by omega) hZ 𝓕 hcorr hN hF₁ hz₁ h1 h3 with hc | ⟨-, hB1⟩
  · exact e189_orth_commuting hodd hQ (by omega) 𝓕 hperf hconj hcorr hF₁ hz₁ hN h1 h3 h4 hc
  · exact e189_orth_projective hodd hQ hdim 𝓕 hperf hconj hcorr hF₁ hz₁ h1 h3 hB1

end Spin8

section Model

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic

variable {p e : ℕ} [Fact p.Prime]

private theorem e189_commutator_eq_of_le' {G : Type} [Group G] {R : Subgroup G}
    (h : R ≤ ⁅R, R⁆) : ⁅R, R⁆ = R :=
  le_antisymm (Subgroup.commutator_le.mpr fun _ ha _ hb =>
    R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) h

theorem e189ModelAt_plus_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p e) : E189ModelAt p e .POmegaPlus 4 := by
  have hn4 : 4 ≤ 4 := le_rfl
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hperf : Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus 4 p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p e)),
      plusDatum 4 (GaloisField p e) hn3⟩ → Gaps.FundPerfect .POmegaPlus M.D →
      E189AtFam M.K (fundamentalSubgroups .POmegaPlus M.D) := by
    intro M hM hP
    subst hM
    refine e189AtFam_spin_of_eight hodd (nondegenerate_polarBilin_quadPlus 4 _) hdim
      (centerScalar_quadPlus hn3) _ ?_ ?_ (fundCorr_plus hp2 hq hn4).1
    · intro R hR
      exact e189_commutator_eq_of_le' (hP R hR)
    · intro R hR g
      exact conjSub_mem_fundamentalSubgroups hR g
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) hperf

end Model

end CFSG.ClassicalInvolution.Asc77
