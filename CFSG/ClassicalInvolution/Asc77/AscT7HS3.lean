module

public import CFSG.ClassicalInvolution.Asc77.AscT7HS2
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
import CFSG.ClassicalInvolution.Asc77.AscIHHelp

public section

namespace CFSG.ClassicalInvolution.Asc77.T7H

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

section Family

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem spin_family_twin_no_sq (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V) (hV4 : ¬ 4 ∣ Module.finrank F V - 2)
    (Φ : Set (Subgroup (spinGroup Q)))
    (hcorr : ∀ R ∈ Φ, R.map (spinAction Q) ∈ fundSet Q) (hperf : ∀ R ∈ Φ, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ Φ, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    ∀ R ∈ Φ, ∀ R' ∈ Φ, R ≠ R' → (∀ a ∈ R, ∀ b ∈ R', a * b = b * a) →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (spinGroup Q), c * c = x * x' → False := by
  intro R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 c hc hcc
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center (ker_spinAction_le_center Q)
      fun r hr hcen => hnc R hR r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center (ker_spinAction_le_center Q)
      fun r hr hcen => hnc R' hR' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  exact spin_twin_sq_false hodd hQ hrange hZ hV hV4 (hperf R hR) (hperf R' hR') (hcorr R hR)
    (hcorr R' hR') hinj hinj' hne hcomm hx hx2 hx1 hx' hx'2 hx'1 hc hcc

end Family

section Models

variable {p e : ℕ} [Fact p.Prime]

theorem spinOdd_twin_no_sq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaOdd 3 p e) :
    ∀ R ∈ ModelFund p .POmegaOdd 3 e, ∀ R' ∈ ModelFund p .POmegaOdd 3 e, R ≠ R' →
      Commutes R R' → ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .POmegaOdd 3 p e Fact.out).K, c * c = x * x' → False := by
  have hn3 : 3 ≤ 3 := le_rfl
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := 3) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := 3) trivial hadm
    (by simp)
  exact spin_family_twin_no_sq hodd (nondegenerate_polarBilin_quadOdd 3 _ h2)
    (range_spinAction_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) (by omega)
    (by rw [hdim]; decide) _ (fundCorr_odd hp2 hq hadm).1 hperf hnc

theorem spinMinus_twin_no_sq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p e) :
    ∀ R ∈ ModelFund p .POmegaMinus 4 e, ∀ R' ∈ ModelFund p .POmegaMinus 4 e, R ≠ R' →
      Commutes R R' → ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .POmegaMinus 4 p e Fact.out).K,
          c * c = x * x' → False := by
  have hn4 : 4 ≤ 4 := le_rfl
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := 4) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := 4) trivial
    hadm (by simp)
  exact spin_family_twin_no_sq hodd
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega) (by rw [hdim]; decide) _
    (fundCorr_minus hp2 hq hadm).1 hperf hnc

theorem spinPlus_twin_no_sq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p e) :
    ∀ R ∈ ModelFund p .POmegaPlus 4 e, ∀ R' ∈ ModelFund p .POmegaPlus 4 e, R ≠ R' →
      Commutes R R' → ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .POmegaPlus 4 p e Fact.out).K, c * c = x * x' → False := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hn4 : 4 ≤ 4 := le_rfl
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p e))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := 4) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := 4) trivial hadm
    (by simp)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p e)),
      plusDatum 4 (GaloisField p e) hn3⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, R ≤ ⁅R, R⁆) →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
      ∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ R' ∈ fundamentalSubgroups .POmegaPlus M.D,
        R ≠ R' → Commutes R R' → ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
          ∀ c ∈ Subgroup.center M.K, c * c = x * x' → False := by
    intro M hM hperf hnc
    subst hM
    exact spin_family_twin_no_sq hodd (nondegenerate_polarBilin_quadPlus 4 _)
      (range_spinAction_quadPlus hn3) (centerScalar_quadPlus hn3) (by omega)
      (by rw [hdim]; decide) _ (fundCorr_plus hp2 hq hn4).1 hperf hnc
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3) hperf hnc

end Models

end CFSG.ClassicalInvolution.Asc77.T7H
