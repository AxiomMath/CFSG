module

public import CFSG.ClassicalInvolution.Asc77.AscBSE4
public import CFSG.ClassicalInvolution.Asc77.AscBSD9
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourModel
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.Asc77.AscBSD8
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSE

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.Asc77 (fund_noncentral_modelUniv)

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime]


theorem spinFund_plus_four (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p e) :
    SpinFund (quadPlus 4 (GaloisField p e))
      (fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p e) (by omega))) := by
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hn3 : 3 ≤ 4 := by omega
  have hn4 : 4 ≤ 4 := le_refl 4
  have hcorr := fundCorr_plus hp2 hq hn4
  have hperf : RouteD.Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus 4 p e Fact.out).D :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := 4) trivial hadm
    (by simp)
  have hsingle := ModelFacts.fundamentalSingleClass .POmegaPlus 4 p e Fact.out trivial hadm
    (by decide) (by decide)
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hnt : Nontrivial (Fin 4 ⊕ Fin 4 → GaloisField p e) :=
    Module.nontrivial_of_finrank_pos (R := GaloisField p e) (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p e)),
      plusDatum 4 (GaloisField p e) hn3⟩ → RouteD.Gaps.FundPerfect .POmegaPlus M.D →
      FundamentalSingleClass .POmegaPlus M.D →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
      SpinFund (quadPlus 4 (GaloisField p e))
        (fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p e) hn3)) := by
    intro M hM hperf hsingle hnc
    subst hM
    exact
      { odd := hodd
        range := range_spinAction_quadPlus hn3
        scalar := Models.Transfer.centerScalar_quadPlus hn3
        nontrivial := hnt
        corr := hcorr.1
        lift := hcorr.2
        perf := hperf
        nc := hnc
        single := hsingle
        conj := fun R hR g => RouteD.conjSub_mem_fundamentalSubgroups hR g }
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) hperf hsingle hnc

theorem exists_fourth_fund_plus (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) {t : StatedLieTag} {n : ℕ}
    (ht : t = .POmegaPlus) (hn : n = 4) (hadm : StatedLieAdmissible t n p e) {X : Type*}
    [Group X] (φ : (modelUniv t n p e Fact.out).K →* X)
    (hφ : φ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K)
    {R₀ R₁ R₂ : Subgroup (modelUniv t n p e Fact.out).K}
    (h₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (h₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (h₂ : R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (e01 : R₀ ≠ R₁) (e02 : R₀ ≠ R₂) (e12 : R₁ ≠ R₂)
    {r₀ r₁ r₂ : (modelUniv t n p e Fact.out).K} (hr₀ : IsInvIn R₀ r₀) (hr₁ : IsInvIn R₁ r₁)
    (hr₂ : IsInvIn R₂ r₂) (p01 : φ r₀ = φ r₁) (p12 : φ r₁ = φ r₂) :
    ∃ R₃ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R₃ ≠ R₀ ∧ R₃ ≠ R₁ ∧
      R₃ ≠ R₂ ∧ ∃ r₃, IsInvIn R₃ r₃ ∧ φ r₃ = φ r₀ := by
  subst ht hn
  have hn3 : 3 ≤ 4 := by omega
  have hsf := spinFund_plus_four hp2 hq hadm
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p e)),
      plusDatum 4 (GaloisField p e) hn3⟩ → ∀ (φ : M.K →* X), φ.ker ≤ Subgroup.center M.K →
      ∀ {R₀ R₁ R₂ : Subgroup M.K}, R₀ ∈ fundamentalSubgroups .POmegaPlus M.D →
      R₁ ∈ fundamentalSubgroups .POmegaPlus M.D → R₂ ∈ fundamentalSubgroups .POmegaPlus M.D →
      R₀ ≠ R₁ → R₀ ≠ R₂ → R₁ ≠ R₂ → ∀ {r₀ r₁ r₂ : M.K}, IsInvIn R₀ r₀ → IsInvIn R₁ r₁ →
      IsInvIn R₂ r₂ → φ r₀ = φ r₁ → φ r₁ = φ r₂ →
      ∃ R₃ ∈ fundamentalSubgroups .POmegaPlus M.D, R₃ ≠ R₀ ∧ R₃ ≠ R₁ ∧ R₃ ≠ R₂ ∧
        ∃ r₃, IsInvIn R₃ r₃ ∧ φ r₃ = φ r₀ := by
    intro M hM φ hφ R₀ R₁ R₂ h₀ h₁ h₂ e01 e02 e12 r₀ r₁ r₂ hr₀ hr₁ hr₂ p01 p12
    subst hM
    obtain ⟨R₃, hR₃, n0, n1, n2, r₃, hr₃, hr₃2, hr₃1, hφ₃⟩ := hsf.exists_fourth φ hφ h₀ h₁ h₂
      e01 e02 e12 hr₀.1 hr₀.2.1 hr₀.2.2 hr₁.1 hr₁.2.1 hr₁.2.2 hr₂.1 hr₂.2.1 hr₂.2.2 p01 p12
    exact ⟨R₃, hR₃, n0, n1, n2, r₃, ⟨hr₃, hr₃2, hr₃1⟩, hφ₃⟩
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) φ hφ h₀ h₁ h₂ e01 e02 e12 hr₀ hr₁ hr₂ p01 p12

end CFSG.ClassicalInvolution.Asc77.BSC.BSE
