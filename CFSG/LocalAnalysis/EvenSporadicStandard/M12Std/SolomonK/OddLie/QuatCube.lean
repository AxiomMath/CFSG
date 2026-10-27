module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Defs
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.M12.Reductions
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child4Final
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.FusionDefs
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
public import CFSG.Walter.JRFacts
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
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open Subgroup

local notation "Q8" => QuaternionGroup 2

theorem card_le_of_sq_mem (A : Subgroup (Q8 × Q8 × Q8))
    (hA : ∀ x ∈ A, x * x = 1 ∨ x * x = (.a 2, .a 2, .a 2)) : Nat.card A ≤ 2 ^ 5 := by
  have hsq : ∀ x : Q8, x * x = 1 → x = 1 ∨ x = .a 2 := by decide
  have hz : (QuaternionGroup.a 2 : Q8) ≠ 1 := by decide
  let π : A →* Q8 := (MonoidHom.fst _ _).comp A.subtype
  have h1 : Nat.card π.ker * Nat.card π.range = Nat.card A :=
    Subgroup.card_ker_mul_card_range π
  have h2 : Nat.card π.range ≤ 8 := by
    calc Nat.card π.range ≤ Nat.card Q8 := Subgroup.card_le_card_group _
      _ = 8 := by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h3 : Nat.card π.ker ≤ 4 := by
    let S : Finset (Q8 × Q8) := ({1, .a 2} : Finset Q8) ×ˢ ({1, .a 2} : Finset Q8)
    have hS : S.card = 4 := by decide
    have hfst : ∀ k : π.ker, ((k : A) : Q8 × Q8 × Q8).1 = 1 := fun k => k.2
    have hk : ∀ k : π.ker,
        (((k : A) : Q8 × Q8 × Q8).2.1, ((k : A) : Q8 × Q8 × Q8).2.2) ∈ S := by
      intro k
      have h := hA _ (k : A).2
      have h0 := hfst k
      set x := ((k : A) : Q8 × Q8 × Q8)
      rcases h with h | h
      · have h1 : x.2.1 * x.2.1 = 1 := congrArg (fun y => y.2.1) h
        have h2 : x.2.2 * x.2.2 = 1 := congrArg (fun y => y.2.2) h
        simp only [S, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨hsq _ h1, hsq _ h2⟩
      · exfalso
        have h1 : x.1 * x.1 = QuaternionGroup.a 2 := congrArg (fun y => y.1) h
        rw [h0, mul_one] at h1
        exact hz h1.symm
    let ψ : π.ker → S := fun k => ⟨_, hk k⟩
    have hψ : Function.Injective ψ := by
      intro k k' hkk'
      have e1 := congrArg (fun s : S => s.1.1) hkk'
      have e2 := congrArg (fun s : S => s.1.2) hkk'
      refine Subtype.ext (Subtype.ext (Prod.ext ?_ (Prod.ext e1 e2)))
      rw [hfst k, hfst k']
    calc Nat.card π.ker ≤ Nat.card S := Nat.card_le_card_of_injective ψ hψ
      _ = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS]
  calc Nat.card A = Nat.card π.ker * Nat.card π.range := h1.symm
    _ ≤ 4 * 8 := Nat.mul_le_mul h3 h2
    _ = 2 ^ 5 := by norm_num

variable {F : Type} [Group F]

theorem false_of_quatCube [Finite F] (hS : ∀ S : Sylow 2 F, ElemFactsIn (S : Subgroup F))
    (φ : Q8 × Q8 × Q8 →* F)
    (hker : ∀ k, φ k = 1 → k = 1 ∨ k = (.a 2, .a 2, .a 2)) : False := by
  have hQ8 : Nat.card Q8 = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcube : Nat.card (Q8 × Q8 × Q8) = 2 ^ 9 := by
    rw [Nat.card_prod, Nat.card_prod, hQ8]
    norm_num
  have hP : IsPGroup 2 (Q8 × Q8 × Q8) :=
    IsPGroup.of_card hcube
  have hR : IsPGroup 2 φ.range := hP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨S₀, hS₀⟩ := hR.exists_le_sylow
  obtain ⟨hcard, -, E₁, hE₁S, hE₁sq, hE₁card, -⟩ := hS S₀
  have hAsq : ∀ k ∈ E₁.comap φ, k * k = 1 ∨ k * k = (.a 2, .a 2, .a 2) := fun k hk =>
    hker _ (by rw [map_mul]; exact hE₁sq _ hk)
  have hAle : Nat.card (E₁.comap φ) ≤ 2 ^ 5 := card_le_of_sq_mem _ hAsq
  have hrel : E₁.relIndex (S₀ : Subgroup F) = 8 := by
    have h := Subgroup.relIndex_mul_card (H := E₁) (K := (S₀ : Subgroup F))
    rw [inf_of_le_left hE₁S, hE₁card, hcard] at h
    omega
  have hidx : (E₁.comap φ).index ≤ 8 := by
    rw [Subgroup.index_comap]
    calc E₁.relIndex φ.range ≤ E₁.relIndex (S₀ : Subgroup F) :=
          Subgroup.relIndex_le_of_le_right hS₀ (by rw [hrel]; norm_num)
      _ = 8 := hrel
  have h := Subgroup.card_mul_index (E₁.comap φ)
  rw [hcube] at h
  have := Nat.mul_le_mul hAle hidx
  rw [h] at this
  norm_num at this

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
