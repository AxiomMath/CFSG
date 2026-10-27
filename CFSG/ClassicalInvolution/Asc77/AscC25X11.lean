module

public import CFSG.ClassicalInvolution.Asc77.AscC25X6
public import CFSG.ClassicalInvolution.Asc77.AscC25X10
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
import CFSG.ClassicalInvolution.ModelFacts.OrthAutOdd
import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus
import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinus
import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.Asc77.AscC25X5
public import CFSG.ClassicalInvolution.Asc77.AscE18FromM
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectD
public import CFSG.ClassicalInvolution.Asc77.AscT7CFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7EFinal3
public import CFSG.ClassicalInvolution.Asc77.AscT7FJ
public import CFSG.ClassicalInvolution.Asc77.AscT7HC5
public import CFSG.ClassicalInvolution.Asc77.AscT7HFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7K11
public import CFSG.ClassicalInvolution.Asc77.AscT7L4
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8
public import CFSG.GH74.GLS.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Open.QuasithinDefs
public import CFSG.StronglyEmbedded.UniqueCoset
public import CFSG.Walter.J1
public import CFSG.Walter.W67.Section5.Lemma57

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups

namespace C25X

section Rows

variable (p : ℕ) [Fact p.Prime]


theorem nc4Spin7 : NC4Spin7 p := by
  intro e hadm hp2 hq
  have hn3 : 3 ≤ 3 := le_rfl
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
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
    (fundCorr_odd hp2 hq hadm).2 hnc (odd_hker2 h2 3)

theorem nc4D4M : NC4D4M p := by
  intro e hadm hp2 hq
  have hn4 : 4 ≤ 4 := le_rfl
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
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
    (fundCorr_minus hp2 hq hadm).2 hnc (minus_hker2 (minusCoeffs_irr p e))

theorem nc4D4P : NC4D4P p := by
  intro e hadm hp2 hq
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p e) hn3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p e))) → r = 1 :=
    fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := 4) trivial hadm
      (by simp)
  have hcorr := fundCorr_plus hp2 hq (le_refl 4)
  have hM : modelUniv .POmegaPlus 4 p e Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (p := p) (f := e) hn3
  show NC4On .POmegaPlus (modelUniv .POmegaPlus 4 p e Fact.out)
  rw [hM]
  exact nc4_of_spin hodd (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3)
    (centerScalar_quadPlus hn3) (by omega) _ hcorr.2 hnc (plus_hker2 4)

end Rows

end C25X

end CFSG.ClassicalInvolution.Asc77
