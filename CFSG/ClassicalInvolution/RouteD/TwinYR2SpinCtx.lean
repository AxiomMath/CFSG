module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinStmt
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.RouteD.Exotic (fundCorr_odd fundCorr_minus fundCorr_plus)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

structure SpinCtx (t : StatedLieTag) {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    (Q : QuadraticForm F (ι → F)) (D : UniversalRootDatum (spinGroup Q)) : Prop where
  hodd : Odd (Nat.card F)
  h5 : 5 ≤ Nat.card F
  hQ : (polarBilin Q).Nondegenerate
  hrange : (spinAction Q).range = elementaryGroup Q
  perfect : Group.IsPerfect (spinGroup Q)
  hZ : CenterScalar Q
  hV : 9 ≤ Module.finrank F (ι → F)
  hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False
  hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q
  hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) = L
  hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆
  hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1

section Models

variable {p e : ℕ} [Fact p.Prime]

theorem spinCtx_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ} (hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    SpinCtx .POmegaOdd (quadOdd n (GaloisField p e)) (oddDatum n (GaloisField p e)) := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p e) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := CFSG.ClassicalInvolution.Asc77.fund_noncentral_modelUniv (p := p) (e := e)
    (t := .POmegaOdd) (n := n) trivial hadm (by simp)
  have hc := fundCorr_odd hp2 hq hadm
  have : Group.IsPerfect (spinGroup (quadOdd n (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  exact ⟨hodd, CFSG.ClassicalInvolution.Asc77.five_le_card_galoisField hq,
    nondegenerate_polarBilin_quadOdd n _ h2, range_spinAction_quadOdd h2 hn3, this,
    centerScalar_quadOdd h2 hn3, by omega, fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj hodd F₁ F₂ h
      omega, hc.1, hc.2, hperf, hnc⟩

theorem spinCtx_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ} (hn5 : 5 ≤ n) (hn3 : 3 ≤ n)
    (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    SpinCtx .POmegaPlus (quadPlus n (GaloisField p e)) (plusDatum n (GaloisField p e) hn3) := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have : Group.IsPerfect (spinGroup (quadPlus n (GaloisField p e))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := CFSG.ClassicalInvolution.Asc77.fund_noncentral_modelUniv (p := p) (e := e)
    (t := .POmegaPlus) (n := n) trivial hadm (by simp)
  have hc := fundCorr_plus hp2 hq hn4
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p e)),
      plusDatum n (GaloisField p e) hn3⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, R ≤ ⁅R, R⁆) →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
        SpinCtx .POmegaPlus (quadPlus n (GaloisField p e)) (plusDatum n (GaloisField p e) hn3) := by
    intro M hM hperf hnc
    subst hM
    exact ⟨hodd, CFSG.ClassicalInvolution.Asc77.five_le_card_galoisField hq,
      nondegenerate_polarBilin_quadPlus n _, range_spinAction_quadPlus hn3, this,
      centerScalar_quadPlus hn3, by omega, fun F₁ F₂ h => by
        have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj hodd F₁ F₂ h
        omega, hc.1, hc.2, hperf, hnc⟩
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3) hperf hnc

theorem spinCtx_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ} (hn5 : 5 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    SpinCtx .POmegaMinus
      (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2)
      (Twisted.minusDatum n (minusCoeffs_irr p e)) := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have : Group.IsPerfect (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := CFSG.ClassicalInvolution.Asc77.fund_noncentral_modelUniv (p := p) (e := e)
    (t := .POmegaMinus) (n := n) trivial hadm (by simp)
  have hc := fundCorr_minus hp2 hq hadm
  show SpinCtx .POmegaMinus (quadMinus n (GaloisField p e) (minusCoeffs p e).1
    (minusCoeffs p e).2) (Twisted.minusDatum n (minusCoeffs_irr p e))
  exact ⟨hodd, CFSG.ClassicalInvolution.Asc77.five_le_card_galoisField hq,
    nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p e),
    range_spinAction_quadMinus hn4 (minusCoeffs_irr p e), this,
    centerScalar_quadMinus hn4 (minusCoeffs_irr p e), by omega,
    fun F₁ F₂ h => CFSG.ClassicalInvolution.Asc77.hproj_quadMinus hp2 hq hn4 F₁ F₂ h,
    hc.1, hc.2, hperf, hnc⟩

end Models

end CFSG.ClassicalInvolution.RouteD.TwinY
