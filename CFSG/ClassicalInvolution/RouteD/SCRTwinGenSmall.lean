module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinModels

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Exotic (fundCorr_odd fundCorr_minus)

section Models

variable {p e : ℕ} [Fact p.Prime]

theorem twinMFGenerationOn_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ} (hn3 : 3 ≤ n)
    (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    TwinMFGenerationOn .POmegaOdd
      ⟨spinGroup (quadOdd n (GaloisField p e)), oddDatum n (GaloisField p e)⟩ := by
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
  exact twinMFGenerationOn_of_spin hodd (CFSG.ClassicalInvolution.Asc77.five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadOdd n _ h2) (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3) (by omega) (fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj hodd F₁ F₂ h
      omega) _ hc.1 hperf hnc

theorem twinMFGenerationOn_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ} (hn4 : 4 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    TwinMFGenerationOn .POmegaMinus
      ⟨spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2),
        Twisted.minusDatum n (minusCoeffs_irr p e)⟩ := by
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
  exact twinMFGenerationOn_of_spin hodd (CFSG.ClassicalInvolution.Asc77.five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun F₁ F₂ h => CFSG.ClassicalInvolution.Asc77.hproj_quadMinus hp2 hq hn4 F₁ F₂ h) _ hc.1
    hperf hnc

theorem twinMFGeneration_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ} (hn3 : 3 ≤ n) :
    TwinMFGeneration p e .POmegaOdd n := by
  have hp : p.Prime := Fact.out
  have he : 1 ≤ e := one_le_of_five_le_pow hq
  have hadm : StatedLieAdmissible .POmegaOdd n p e := ⟨hp, he, hn3, hp2⟩
  exact twinMFGeneration_of_on
    (show TwinMFGenerationOn .POmegaOdd ⟨spinGroup (quadOdd n (GaloisField p e)),
      oddDatum n (GaloisField p e)⟩ from twinMFGenerationOn_odd hp2 hq hn3 hadm)

theorem twinMFGeneration_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ} (hn4 : 4 ≤ n) :
    TwinMFGeneration p e .POmegaMinus n := by
  have hp : p.Prime := Fact.out
  have he : 1 ≤ e := one_le_of_five_le_pow hq
  have hadm : StatedLieAdmissible .POmegaMinus n p e := ⟨hp, he, hn4⟩
  exact twinMFGeneration_of_on
    (show TwinMFGenerationOn .POmegaMinus
      ⟨spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2),
        Twisted.minusDatum n (minusCoeffs_irr p e)⟩ from twinMFGenerationOn_minus hp2 hq hn4 hadm)

end Models

end CFSG.ClassicalInvolution.RouteD.TwinY
