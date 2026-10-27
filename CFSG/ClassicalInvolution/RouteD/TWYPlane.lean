module

public import CFSG.ClassicalInvolution.Asc77.AscT7HS2
public import CFSG.ClassicalInvolution.RouteD.TWYMat
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Asc77.T7H
  CFSG.GroupTheory.WeirSylow QuadraticMap
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Plane

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem incl_mem_minusSp_twinInv (fr : OFrame Q) (A A' : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    fr.incl X ∈ minusSp (twinInv fr A A') ↔
      (A : Matrix (Fin 2) (Fin 2) F) * X * sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) = -X := by
  rw [mem_minusSp, twinInv_incl, ← map_neg]
  exact ⟨fun h => fr.incl_injective h, fun h => by rw [h]⟩

theorem exists_isotropic_minusSp_twinInv_iff (h2 : (2 : F) ≠ 0) (fr : OFrame Q) {A A' : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) :
    (∃ w ∈ minusSp (twinInv fr A A'), w ≠ 0 ∧ Q w = 0) ↔ IsSquare (-1 : F) := by
  have hB : sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) * sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) =
      -1 := sigmaLin_sq hA'
  have hBd : (sigmaLin (A' : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
    rw [det_sigmaLin]
    exact A'.det_coe
  rw [← mat_exists_isotropic_iff h2 hA A.det_coe hB hBd]
  constructor
  · rintro ⟨w, hw, hw0, hQw⟩
    have hspan : w ∈ fr.span := by
      have := hw
      rw [minusSp_twinInv_eq h2 fr] at this
      exact this.1
    have hw' := fr.mem_span_iff.mp hspan
    refine ⟨fr.coords w, ?_, ?_, ?_⟩
    · intro h
      apply hw0
      rw [hw', h, map_zero]
    · rw [← fr.Q_incl, ← hw']
      exact hQw
    · refine (incl_mem_minusSp_twinInv fr A A' (fr.coords w)).mp ?_
      rw [← hw']
      exact hw
  · rintro ⟨X, hX, hXd, hAX⟩
    refine ⟨fr.incl X, (incl_mem_minusSp_twinInv fr A A' X).mpr hAX, ?_, ?_⟩
    · intro h
      exact hX (fr.incl_injective (by rw [h, map_zero]))
    · rw [fr.Q_incl, hXd]

theorem isPlusType_restrict_iff_of_finrank_two {W : Submodule F V}
    (hW : Module.finrank F W = 2) :
    IsPlusType (Q.restrict W) ↔ ∃ w ∈ W, w ≠ 0 ∧ Q w = 0 := by
  constructor
  · rintro ⟨S, hS, hSs⟩
    have h1 : Module.finrank F S = 1 := by omega
    have hne : S ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at h1
      omega
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨(s : V), s.2, fun h => hs0 (Subtype.ext h), ?_⟩
    have := hSs s hsS
    simpa using this
  · rintro ⟨w, hwW, hw0, hQw⟩
    have hw' : (⟨w, hwW⟩ : W) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
    refine ⟨Submodule.span F {(⟨w, hwW⟩ : W)}, ?_, ?_⟩
    · rw [finrank_span_singleton hw', hW]
    · intro x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      show Q ((c • (⟨w, hwW⟩ : W) : W) : V) = 0
      rw [Submodule.coe_smul, QuadraticMap.map_smul, hQw, smul_zero]

theorem isPlusType_restrict_minusSp_twinInv_iff (h2 : (2 : F) ≠ 0) (fr : OFrame Q) {A A' : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1)
    (hW : Module.finrank F (minusSp (twinInv fr A A')) = 2) :
    IsPlusType (Q.restrict (minusSp (twinInv fr A A'))) ↔ IsSquare (-1 : F) := by
  rw [isPlusType_restrict_iff_of_finrank_two hW]
  exact exists_isotropic_minusSp_twinInv_iff h2 fr hA hA'

end Plane

end CFSG.ClassicalInvolution.RouteD.TWY
