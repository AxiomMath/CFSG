module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscBSD7
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Exotic (fundCorr_odd fundCorr_minus)
open CFSG.ClassicalInvolution.RouteD (ModelFund)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundPerfect_modelUniv)
open CFSG.ClassicalInvolution.Asc77 (finrank_eq_eight_of_proj hproj_quadMinus
  fund_noncentral_modelUniv)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]


theorem fundTwoBound_odd_three : FundTwoBound p .POmegaOdd 3 := by
  intro e hp2 hq hadm R₀ R₁ R₂ h₀ h₁ h₂ r₀ r₁ r₂ hr₀ hr₁ hr₂ h01 h12
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hn3 : 3 ≤ 3 := le_refl 3
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have hperf := fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := 3) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := 3) trivial hadm
    (by simp)
  have : Nontrivial (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) :=
    Module.nontrivial_of_finrank_pos (R := GaloisField p e) (by omega)
  exact spin_two_bound (Q := quadOdd 3 (GaloisField p e)) hodd (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3)
    (fun F₁ F₂ h => by
      have := finrank_eq_eight_of_proj hodd F₁ F₂ h
      omega)
    (fundCorr_odd hp2 hq hadm).1 hperf hnc h₀ h₁ h₂ hr₀ hr₁ hr₂ h01 h12

theorem fundTwoBound_minus_four : FundTwoBound p .POmegaMinus 4 := by
  intro e hp2 hq hadm R₀ R₁ R₂ h₀ h₁ h₂ r₀ r₁ r₂ hr₀ hr₁ hr₂ h01 h12
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hn4 : 4 ≤ 4 := le_refl 4
  have hdim : Module.finrank (GaloisField p e)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have hperf := fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := 4) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := 4) trivial
    hadm (by simp)
  have : Nontrivial (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) :=
    Module.nontrivial_of_finrank_pos (R := GaloisField p e) (by omega)
  exact spin_two_bound (Q := quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2) hodd (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e))
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h)
    (fundCorr_minus hp2 hq hadm).1 hperf hnc h₀ h₁ h₂ hr₀ hr₁ hr₂ h01 h12

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
