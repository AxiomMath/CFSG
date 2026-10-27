module

public import CFSG.ClassicalInvolution.Asc77.AscC25J19
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainU
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.OrthAut
open CFSG.ClassicalInvolution.Asc77.C25X
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three neZero_of_pow_eq_three)
open CFSG.ClassicalInvolution.ModelFacts (odd_natCard_galoisField_of_pow_eq_three)
open scoped MatrixGroups

section Rows

variable {p : ℕ} [Fact p.Prime]


theorem nc4Spin7_three {e : ℕ} (h3 : p ^ e = 3) (hadm : StatedLieAdmissible .POmegaOdd 3 p e) :
    NC4At p .POmegaOdd 3 e := by
  have hp2 := ne_two_of_pow_eq_three h3
  have hn3 : 3 ≤ 3 := le_rfl
  have hodd := odd_natCard_galoisField_of_pow_eq_three h3
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) =
      2 * 3 + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := 3) trivial hadm
    (by simp)
  show NC4On .POmegaOdd ⟨spinGroup (quadOdd 3 (GaloisField p e)), oddDatum 3 (GaloisField p e)⟩
  exact nc4_of_spin hodd (nondegenerate_polarBilin_quadOdd 3 _ h2)
    (range_spinAction_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) (by omega) _
    (fundCorr_odd3 h3 hadm).2 hnc (odd_hker2 h2 3)

theorem nc4D4M_three {e : ℕ} (h3 : p ^ e = 3) (hadm : StatedLieAdmissible .POmegaMinus 4 p e) :
    NC4At p .POmegaMinus 4 e := by
  have hn4 : 4 ≤ 4 := le_rfl
  have hodd := odd_natCard_galoisField_of_pow_eq_three h3
  have hdim : Module.finrank (GaloisField p e)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := 4) trivial
    hadm (by simp)
  show NC4On .POmegaMinus ⟨spinGroup (quadMinus 4 (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum 4 (minusCoeffs_irr p e)⟩
  exact nc4_of_spin hodd
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega) _
    (fundCorr_minus3 h3 hadm).2 hnc (minus_hker2 (minusCoeffs_irr p e))

theorem nc4D4P_three {e : ℕ} (h3 : p ^ e = 3) (hadm : StatedLieAdmissible .POmegaPlus 4 p e) :
    NC4At p .POmegaPlus 4 e := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hodd := odd_natCard_galoisField_of_pow_eq_three h3
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p e) hn3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p e))) → r = 1 :=
    fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := 4) trivial hadm
      (by simp)
  have hcorr := fundCorr_plus3 h3 (le_refl 4)
  have hM : modelUniv .POmegaPlus 4 p e Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (p := p) (f := e) hn3
  show NC4On .POmegaPlus (modelUniv .POmegaPlus 4 p e Fact.out)
  rw [hM]
  exact nc4_of_spin hodd (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3)
    (centerScalar_quadPlus hn3) (by omega) _ hcorr.2 hnc (plus_hker2 4)

end Rows

end CFSG.ClassicalInvolution.Asc77.C25J
