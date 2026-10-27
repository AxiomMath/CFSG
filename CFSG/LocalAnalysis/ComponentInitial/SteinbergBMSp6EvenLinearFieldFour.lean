module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverSylow
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullAffine
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBM

open Subgroup LinearFlag FieldFourCover GL3TwoFixedModel

variable {k : Type} [Field k]

theorem projUnip_le_centralizer_projW :
    projUnip k ≤ centralizer {proj 3 k (unipU k 0 0 1)} := by
  intro x hx
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, unipU_mul, unipU_mul]
  congr 2 <;> ring

section FieldFour

variable [Finite k] (hk : Nat.card k = 4)
include hk

omit [Finite k] hk in
theorem id_ker_facts :
    (MonoidHom.id (projectiveSL 3 k)).ker ≤ center (projectiveSL 3 k) ∧
      CFSG.IsElementaryAbelian 2 (MonoidHom.id (projectiveSL 3 k)).ker := by
  have h1 : ∀ x ∈ (MonoidHom.id (projectiveSL 3 k)).ker, x = 1 := fun x hx => hx
  refine ⟨fun x hx => ?_, isElementaryAbelian_of_sq_eq_one fun x hx => ?_⟩
  · rw [h1 x hx]
    exact one_mem _
  · rw [h1 x hx, one_pow]

theorem exists_sylow_eq_projUnip :
    ∃ S : Sylow 2 (projectiveSL 3 k), (S : Subgroup (projectiveSL 3 k)) = projUnip k := by
  obtain ⟨hCZ, hC⟩ := id_ker_facts (k := k)
  have : Finite (projectiveSL 3 k) := inferInstance
  obtain ⟨-, -, ⟨S, hS⟩, -⟩ := field_four_central_two_cover_parabolic_normalizers hk
    (MonoidHom.id _) Function.surjective_id hCZ hC
  exact ⟨S, hS.trans (Subgroup.comap_id _)⟩

theorem exists_conj_le_projUnip {E : Subgroup (projectiveSL 3 k)} (hE : IsPGroup 2 E) :
    ∃ g : projectiveSL 3 k, ∀ x ∈ E, g⁻¹ * x * g ∈ projUnip k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := exists_sylow_eq_projUnip hk
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 k) S₀ S
  refine ⟨g, fun x hx => ?_⟩
  have hxS : x ∈ ((g • S₀ : Sylow 2 (projectiveSL 3 k)) : Subgroup (projectiveSL 3 k)) := by
    rw [hg]
    exact hS hx
  rw [mem_smul_sylow_iff, hS₀] at hxS
  exact hxS

theorem exists_conj_eq_projW {x : projectiveSL 3 k} (hx : orderOf x = 2) :
    ∃ p : projectiveSL 3 k, p * x * p⁻¹ = proj 3 k (unipU k 0 0 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_le_projUnip hk hzp
  set y := g⁻¹ * x * g with hy
  have hyU : y ∈ projUnip k := hg x (mem_zpowers x)
  have hy2 : y ^ 2 = 1 := by
    rw [hy, show g⁻¹ * x * g = MulAut.conj g⁻¹ x by rw [MulAut.conj_apply, inv_inv], ← map_pow,
      ← hx, pow_orderOf_eq_one, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    have hx1 : x = 1 := by
      have : g⁻¹ * x * g = 1 := h
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [this, mul_one, mul_inv_cancel]
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hw1 : proj 3 k (unipU k 0 0 1) ≠ 1 := proj_unipU_ne_one (by simp)
  have key : ∀ i : Fin 2, y ∈ projRad k i →
      ∃ p : projectiveSL 3 k, p * x * p⁻¹ = proj 3 k (unipU k 0 0 1) := by
    intro i hyi
    obtain ⟨p, hp⟩ := projRad_transitive i hyi
      (projCenterW_le_projRad i (mem_projCenterW.2 ⟨1, rfl⟩)) hy1 hw1
    refine ⟨p * g⁻¹, ?_⟩
    rw [← hp, hy]
    group
  rcases mem_projRad_of_sq_eq_one hk hyU hy2 with h | h
  · exact key 0 h
  · exact key 1 h

theorem exists_conj_projRad_le {E : Subgroup (projectiveSL 3 k)} (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hcard : 16 ≤ Nat.card E) :
    Nat.card E = 16 ∧ ∃ (p : projectiveSL 3 k) (i : Fin 2), ∀ r ∈ projRad k i, p * r * p⁻¹ ∈ E := by
  obtain ⟨hCZ, hC⟩ := id_ker_facts (k := k)
  have hEp : IsPGroup 2 E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE2 x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_projUnip hk hEp
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'card : Nat.card E' = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).toEquiv).symm
  have hE'U : E' ≤ (projUnip k).comap (MonoidHom.id _) := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hg x hx
    change (MulAut.conj g⁻¹) x ∈ projUnip k
    rw [MulAut.conj_apply, inv_inv]
    exact h
  have hE'el : CFSG.IsElementaryAbelian 2 E' := isElementaryAbelian_of_sq_eq_one (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE2 x hx, map_one])
  have hk16 : ∀ i : Fin 2, Nat.card (projRad k i) = 16 := fun i => by
    rw [card_projRad, hk]
  have key : ∀ i : Fin 2, E' ≤ (projRad k i).comap (MonoidHom.id _) →
      Nat.card E = 16 ∧
        ∃ (p : projectiveSL 3 k) (i : Fin 2), ∀ r ∈ projRad k i, p * r * p⁻¹ ∈ E := by
    intro i hi
    have hle : E' ≤ projRad k i := hi
    have heq : E' = projRad k i :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hk16, hE'card]; exact hcard)
    have hEc : Nat.card E = 16 := by
      rw [← hE'card, heq]
      exact hk16 i
    refine ⟨hEc, g, i, fun r hr => ?_⟩
    rw [← heq] at hr
    obtain ⟨x, hx, hxr⟩ := hr
    rw [← hxr]
    change g * ((MulAut.conj g⁻¹) x) * g⁻¹ ∈ E
    rw [MulAut.conj_apply, inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    exact hx
  rcases le_or_le_of_isElementaryAbelian hk Function.surjective_id hCZ hC hE'U hE'el with h | h
  · exact key 0 h
  · exact key 1 h

omit [Finite k] hk in
theorem binaryEmbed_glTransThreeOne [CharP k 2] :
    binaryEmbed k (rfl : 3 = 3) glTransThreeOne = proj 3 k (unipU k 0 0 1) := by
  rw [binaryEmbed_apply]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipU, glTransThreeOne]

omit [Finite k] hk in
theorem binaryEmbed_glTransTwoOne [CharP k 2] :
    binaryEmbed k (rfl : 3 = 3) glTransTwoOne = proj 3 k (unipU k 1 0 0) := by
  rw [binaryEmbed_apply]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipU, glTransTwoOne]

omit [Finite k] hk in
theorem binaryEmbed_glTransThreeTwo [CharP k 2] :
    binaryEmbed k (rfl : 3 = 3) glTransThreeTwo = proj 3 k (unipU k 0 1 0) := by
  rw [binaryEmbed_apply]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipU, glTransThreeTwo]

end FieldFour

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBM
