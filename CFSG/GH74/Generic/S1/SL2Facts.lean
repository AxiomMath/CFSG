module

public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.GLS.Classes
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.RankThree.Classical.OddQuadraticFrame
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
public import CFSG.LieType.Universal.Unitary.Clause0
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.Data.Matrix.Composition
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit

public section

open Subgroup CFSG CFSG.LocalCores CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

variable {X : Type} [Group X] {V : Subgroup X} {q : ℕ}

theorem exists_sl2_equiv (hV : CFSG.GH74.GLS.HasSL2Model ↥V (fun q' => q' = q)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧ Nonempty (SL(2, F) ≃* ↥V) := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hV
  exact ⟨F, inferInstance, inferInstance, hFq,
    ⟨(specialLinearGroupEquivStatedSL 2 F).trans e.symm⟩⟩

theorem isQuasisimple_of_sl2 (h4 : 4 ≤ q) (hV : CFSG.GH74.GLS.HasSL2Model ↥V (fun q' => q' = q)) :
    CFSG.IsQuasisimple ↥V := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := exists_sl2_equiv hV
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c (by rw [hFq]; exact h4))

theorem sl2_involution_facts (hq : Odd q) (hV : CFSG.GH74.GLS.HasSL2Model ↥V (fun q' => q' = q)) :
    ∃ t : X, t ∈ V ∧ orderOf t = 2 ∧ (∀ v ∈ V, v * v = 1 → v = 1 ∨ v = t) ∧
      (∀ z ∈ V, (∀ w ∈ V, z * w = w * z) → z = 1 ∨ z = t) := by
  obtain ⟨F, _, _, hFq, ⟨e'⟩⟩ := exists_sl2_equiv hV
  have hodd : Odd (Nat.card F) := hFq ▸ hq
  have h2F : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hF2 : ringChar F ≠ 2 := by
    intro h
    apply h2F
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero
  have hneg : (-1 : SL(2, F)) * (-1) = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp
  have hne : (-1 : SL(2, F)) ≠ 1 := CFSG.GH74.KGroups.L3Eps.neg_one_ne_one h2F
  refine ⟨(e' (-1) : X), (e' (-1)).2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e']
    exact orderOf_eq_prime (by rw [sq]; exact hneg) hne
  · intro v hv hv2
    have hw : e'.symm ⟨v, hv⟩ * e'.symm ⟨v, hv⟩ = 1 := by
      rw [← map_mul]
      have : (⟨v, hv⟩ : ↥V) * ⟨v, hv⟩ = 1 := Subtype.ext hv2
      rw [this, map_one]
    rcases CFSG.GH74.KGroups.L3Eps.sl2c_sq_eq_one hF2 hw with h | h
    · left
      have : (⟨v, hv⟩ : ↥V) = 1 := by simpa using congrArg e' h
      exact congrArg Subtype.val this
    · right
      have : (⟨v, hv⟩ : ↥V) = e' (-1) := by simpa using congrArg e' h
      exact congrArg Subtype.val this
  · intro z hz hzc
    have hw : e'.symm ⟨z, hz⟩ ∈ center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply e'.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (hzc (e' x : X) (e' x).2).symm
    rcases CFSG.GH74.KGroups.L3Eps.sl2c_center_eq hw with h | h
    · left
      have : (⟨z, hz⟩ : ↥V) = 1 := by simpa using congrArg e' h
      exact congrArg Subtype.val this
    · right
      have : (⟨z, hz⟩ : ↥V) = e' (-1) := by simpa using congrArg e' h
      exact congrArg Subtype.val this

end CFSG.GH74.Generic.S1
