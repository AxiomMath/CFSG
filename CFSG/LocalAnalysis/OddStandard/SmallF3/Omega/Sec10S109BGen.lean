module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
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
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec10B_range_isElemAbelian {U A : Type} [Group U] [Group A] (φ : U →* A)
    (hc : ∀ a b : U, φ (a * b * a⁻¹ * b⁻¹) = 1) (hs : ∀ a : U, φ (a * a) = 1) :
    CFSG.Open.IsElemAbelian 2 φ.range := by
  refine ⟨isMulCommutative_iff.mpr fun a b => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    refine Subtype.ext ?_
    show (a : A) * b = b * a
    rw [← hx, ← hy]
    have h := hc x y
    simp only [map_mul, map_inv] at h
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)
  · obtain ⟨u, rfl⟩ := hx
    rw [pow_two, ← map_mul]
    exact hs u

theorem sec10B_mem_zpowers_of_conj {z c w : G} (hc : c * z = z * c)
    (hw : c * w * c⁻¹ ∈ zpowers z) : w ∈ zpowers z := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  have e1 : c * w = c * z ^ n := by
    calc c * w = (c * w * c⁻¹) * c := by group
      _ = z ^ n * c := by rw [← hn]
      _ = c * z ^ n := ((Commute.zpow_right hc n).eq).symm
  exact (mul_left_cancel e1).symm

theorem sec10B_card_conjugate (H : Subgroup G) (c : G) :
    Nat.card ↥(CFSG.conjugate H c) = Nat.card ↥H := by
  rw [CFSG.conjugate]
  exact Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective

theorem sec10B_conjugate_eq {W : Subgroup G} {c : G} (hc : c ∈ normalizer (W : Set G)) :
    CFSG.conjugate W c = W := by
  ext x
  rw [mem_conjugate_iff']
  exact ((Subgroup.mem_normalizer_iff.mp hc) x).symm

theorem sec10B_card_range_ge {U A : Type} [Group U] [Group A] (φ : U →* A)
    (hker : Nat.card ↥φ.ker ≤ 2) (hU : 64 ≤ Nat.card U) : 32 ≤ Nat.card ↥φ.range := by
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 := Nat.mul_le_mul_right (Nat.card ↥φ.range) hker
  omega

end CFSG.OddStandard.SmallF3.Omega
