module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Pair
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLGraph
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorAut
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Frame
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitCase
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
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
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks
open CFSG.ComponentClassification.Burgoyne.PSL (graphLift toGL_graphLift conjAut_mul_dualAut_proj)

variable {k : Type} [Field k]

@[expose] def uuSL (c : k) : SpecialLinearGroup (Fin 2) k := ⟨uu c, det_uu c⟩

@[expose] def llSL (c : k) : SpecialLinearGroup (Fin 2) k := ⟨ll c, det_ll c⟩

theorem graphLift_mul (B : GL (Fin 4) k) (X : SpecialLinearGroup (Fin 4) k) :
    ((graphLift B X : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *
        (B : Matrix (Fin 4) (Fin 4) k) =
      (B : Matrix (Fin 4) (Fin 4) k) *
        ((X⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)ᵀ := by
  have h := toGL_graphLift B X
  have h2 : SpecialLinearGroup.toGL (graphLift B X) * B =
      B * GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL X) := by
    rw [h, inv_mul_cancel_right]
  have h3 := congrArg (fun M : GL (Fin 4) k => (M : Matrix (Fin 4) (Fin 4) k)) h2
  simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
    GeneralLinearGroup.coe_inverseTranspose] at h3
  rw [h3, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix]

theorem exists_smul_bdR_of_mem {Y : SpecialLinearGroup (Fin 4) k} (h : proj 4 k Y ∈ factorR k) :
    ∃ (c : k) (W : Matrix (Fin 2) (Fin 2) k),
      (Y : Matrix (Fin 4) (Fin 4) k) = c • bd 1 W := by
  obtain ⟨W, hW⟩ := h
  rw [MonoidHom.comp_apply, proj_eq_proj_iff, mem_scalars] at hW
  obtain ⟨c, -, hc⟩ := hW
  refine ⟨c, W, ?_⟩
  have e : Y = bdR k W * ((bdR k W)⁻¹ * Y) := by group
  rw [e, Matrix.SpecialLinearGroup.coe_mul, hc, coe_bdR]
  ext i j
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

theorem exists_smul_bdL_of_mem {Y : SpecialLinearGroup (Fin 4) k} (h : proj 4 k Y ∈ factorL k) :
    ∃ (c : k) (W : Matrix (Fin 2) (Fin 2) k),
      (Y : Matrix (Fin 4) (Fin 4) k) = c • bd W 1 := by
  obtain ⟨W, hW⟩ := h
  rw [MonoidHom.comp_apply, proj_eq_proj_iff, mem_scalars] at hW
  obtain ⟨c, -, hc⟩ := hW
  refine ⟨c, W, ?_⟩
  have e : Y = bdL k W * ((bdL k W)⁻¹ * Y) := by group
  rw [e, Matrix.SpecialLinearGroup.coe_mul, hc, coe_bdL]
  ext i j
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

theorem uuSL_inv (c : k) : (uuSL c)⁻¹ = uuSL (-c) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  show uu c * uu (-c) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uu, Matrix.mul_apply, Fin.sum_univ_two]

theorem llSL_inv (c : k) : (llSL c)⁻¹ = llSL (-c) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  show ll c * ll (-c) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ll, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_ne_zero_GL (B : GL (Fin 4) k) : (B : Matrix (Fin 4) (Fin 4) k).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero

theorem eq_zero_aux₁ {c x y : k} (hx : c * x = x) (hy : c * y = y + x * -1) : x = 0 := by
  by_cases hc : c = 1
  · subst hc
    linear_combination hy
  · have h : (c - 1) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc)

theorem eq_zero_aux₂ {c x y : k} (hy : c * y = y) (hx : c * x = y * -1 + x) : y = 0 := by
  by_cases hc : c = 1
  · subst hc
    linear_combination hx
  · have h : (c - 1) * y = 0 := by linear_combination hy
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc)

local macro "six_norm" " at " h:(ppSpace colGt term:max)+ : tactic =>
  `(tactic| simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply,
    Matrix.transpose_apply, bd, uuSL, llSL, uu, ll, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val, Matrix.one_apply_eq, Matrix.one_apply_ne, Fin.isValue, ne_eq, Fin.reduceEq,
    not_false_eq_true, mul_zero, zero_mul, mul_one, add_zero, zero_add, smul_eq_mul] at $h*)

theorem ul_eq_zero_of_swap {B : GL (Fin 4) k}
    (h1 : (conjAut 4 k B * dualAut 4 k) (proj 4 k (bdL k (uuSL 1))) ∈ factorR k)
    (h2 : (conjAut 4 k B * dualAut 4 k) (proj 4 k (bdL k (llSL 1))) ∈ factorR k) :
    (B : Matrix (Fin 4) (Fin 4) k) 0 0 = 0 ∧ (B : Matrix (Fin 4) (Fin 4) k) 0 1 = 0 ∧
      (B : Matrix (Fin 4) (Fin 4) k) 1 0 = 0 ∧ (B : Matrix (Fin 4) (Fin 4) k) 1 1 = 0 := by
  rw [conjAut_mul_dualAut_proj] at h1 h2
  obtain ⟨c, W, hc⟩ := exists_smul_bdR_of_mem h1
  obtain ⟨c', W', hc'⟩ := exists_smul_bdR_of_mem h2
  have e1 := graphLift_mul B (bdL k (uuSL 1))
  have e2 := graphLift_mul B (bdL k (llSL 1))
  rw [hc, ← map_inv, uuSL_inv, coe_bdL] at e1
  rw [hc', ← map_inv, llSL_inv, coe_bdL] at e2
  set Bm := (B : Matrix (Fin 4) (Fin 4) k)
  have a00 := congrFun (congrFun e1 0) 0
  have a01 := congrFun (congrFun e1 0) 1
  have a10 := congrFun (congrFun e1 1) 0
  have a11 := congrFun (congrFun e1 1) 1
  have b00 := congrFun (congrFun e2 0) 0
  have b01 := congrFun (congrFun e2 0) 1
  have b10 := congrFun (congrFun e2 1) 0
  have b11 := congrFun (congrFun e2 1) 1
  six_norm at a00 a01 a10 a11 b00 b01 b10 b11
  exact ⟨eq_zero_aux₂ b00 b01, eq_zero_aux₁ a01 a00, eq_zero_aux₂ b10 b11, eq_zero_aux₁ a11 a10⟩

theorem lr_eq_zero_of_swap {B : GL (Fin 4) k}
    (h1 : (conjAut 4 k B * dualAut 4 k) (proj 4 k (bdR k (uuSL 1))) ∈ factorL k)
    (h2 : (conjAut 4 k B * dualAut 4 k) (proj 4 k (bdR k (llSL 1))) ∈ factorL k) :
    (B : Matrix (Fin 4) (Fin 4) k) 2 2 = 0 ∧ (B : Matrix (Fin 4) (Fin 4) k) 2 3 = 0 ∧
      (B : Matrix (Fin 4) (Fin 4) k) 3 2 = 0 ∧ (B : Matrix (Fin 4) (Fin 4) k) 3 3 = 0 := by
  rw [conjAut_mul_dualAut_proj] at h1 h2
  obtain ⟨c, W, hc⟩ := exists_smul_bdL_of_mem h1
  obtain ⟨c', W', hc'⟩ := exists_smul_bdL_of_mem h2
  have e1 := graphLift_mul B (bdR k (uuSL 1))
  have e2 := graphLift_mul B (bdR k (llSL 1))
  rw [hc, ← map_inv, uuSL_inv, coe_bdR] at e1
  rw [hc', ← map_inv, llSL_inv, coe_bdR] at e2
  set Bm := (B : Matrix (Fin 4) (Fin 4) k)
  have a22 := congrFun (congrFun e1 2) 2
  have a23 := congrFun (congrFun e1 2) 3
  have a32 := congrFun (congrFun e1 3) 2
  have a33 := congrFun (congrFun e1 3) 3
  have b22 := congrFun (congrFun e2 2) 2
  have b23 := congrFun (congrFun e2 2) 3
  have b32 := congrFun (congrFun e2 3) 2
  have b33 := congrFun (congrFun e2 3) 3
  six_norm at a22 a23 a32 a33 b22 b23 b32 b33
  exact ⟨eq_zero_aux₂ b22 b23, eq_zero_aux₁ a23 a22, eq_zero_aux₂ b32 b33, eq_zero_aux₁ a33 a32⟩

end Catalog7L4

end CFSG.ComponentClassification.GSThmB
