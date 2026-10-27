module

public import CFSG.GH74.Generic.Front.SpFld
public import CFSG.GH74.Generic.ClassicalCerts
public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Assembly.LowTwoRank Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.GH74.Filter.ClassicalOdd
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (conjAut_mul_fieldAut_eq_one_iff)

variable {F : Type} [Field F]

theorem card_le_four_sp4 (h2 : (2 : F) ≠ 0) {E : Subgroup (StatedSp 2 F)}
    (hE : CFSG.IsElementaryAbelian 2 E) : Nat.card E ≤ 4 := by
  classical
  let f : E → GL (Fin 2 ⊕ Fin 2) F := fun b => ((b : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)
  have hf : Function.Injective f := fun b b' h => Subtype.ext (Subtype.ext h)
  have := hE
  have hsq : ∀ b : E, f b * f b = 1 := fun b => by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) (b : StatedSp 2 F) b.2
    have h' := congrArg Subtype.val h
    simpa [f, sq] using h'
  have hcomm : ∀ b b' : E, f b * f b' = f b' * f b := fun b b' => by
    have h := hE.is_comm.comm b b'
    have h' := congrArg (fun x : E => ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)) h
    simpa [f] using h'
  have hmem : ∀ b : E, f b ∈ StatedSp 2 F := fun b => (b : StatedSp 2 F).2
  obtain ⟨a, ha⟩ : ∃ a : GL (Fin 2 ⊕ Fin 2) F,
      ∀ b : E, f b ∈ ({1, -1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) F)) := by
    by_cases hall : ∀ b : E, f b = 1 ∨ f b = -1
    · refine ⟨1, fun b => ?_⟩
      rcases hall b with h | h <;> simp [h]
    · push Not at hall
      obtain ⟨b₀, hb₁, hbm⟩ := hall
      refine ⟨f b₀, fun b => ?_⟩
      rcases CFSG.RankThree.SubgroupLists.eq_of_commute_involution h2 (hmem b₀) (hmem b)
          (hsq b₀) (hsq b) (hcomm b₀ b) hb₁ hbm with h | h | h | h <;> simp [h]
  calc Nat.card E ≤ Nat.card ({1, -1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) F)) :=
        Nat.card_le_card_of_injective (fun b => ⟨f b, ha b⟩)
          (fun b b' h => hf (Subtype.mk.inj h))
    _ = ({1, -1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) F)).card := Nat.card_eq_finsetCard _
    _ ≤ 4 := Finset.card_le_four

theorem eq_one_of_conjSp_mul_fieldSp_eq [Finite F] {A C : gsp 2 F} {σ : F ≃+* F}
    (h : conjSp 2 F A * fieldSp 2 F σ = conjSp 2 F C) : σ = 1 := by
  have hP : conjAut 2 F (C⁻¹ * A) * fieldAut 2 F σ = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨g, rfl⟩ : ∃ g, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F g = x :=
      QuotientGroup.mk'_surjective _ x
    rw [MulAut.mul_apply, MulAut.one_apply, fieldAut_proj, conjAut_proj]
    congr 1
    have hg := congrArg (fun α : MulAut ↥(StatedSp 2 F) => α g) h
    simp only [MulAut.mul_apply] at hg
    rw [map_mul, MulAut.mul_apply, hg, map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  exact ((conjAut_mul_fieldAut_eq_one_iff (by norm_num) _ σ).1 hP).1

theorem multiplier_scalarGsp (b : Fˣ) :
    multiplier 2 F (CFSG.RankThree.Classical.SteinbergBY.scalarGsp b) = b * b := by
  refine multiplier_eq _ ?_
  rw [CFSG.RankThree.Classical.SteinbergBY.coe_scalarGsp, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_transpose, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, Units.val_mul]

theorem conjSp_eq_conj_of_multiplier {A : gsp 2 F} {l : Fˣ} (h : multiplier 2 F A = l * l) :
    ∃ g : StatedSp 2 F, conjSp 2 F A = MulAut.conj g := by
  set A' : gsp 2 F := A * CFSG.RankThree.Classical.SteinbergBY.scalarGsp l⁻¹ with hA'
  have hm : multiplier 2 F A' = 1 := by
    rw [hA', map_mul, h, multiplier_scalarGsp]
    group
  have hmem : (A' : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := by
    have h1 : A' ∈ (multiplier 2 F).ker := MonoidHom.mem_ker.mpr hm
    rw [ker_multiplier] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  refine ⟨⟨A', hmem⟩, ?_⟩
  have hA : A = A' * CFSG.RankThree.Classical.SteinbergBY.scalarGsp l := by
    apply Subtype.ext
    rw [hA', Subgroup.coe_mul, Subgroup.coe_mul, CFSG.RankThree.Classical.SteinbergBY.coe_scalarGsp,
      CFSG.RankThree.Classical.SteinbergBY.coe_scalarGsp, mul_assoc, ← map_mul, inv_mul_cancel,
      map_one, mul_one]
  rw [hA, map_mul, CFSG.GH74.Generic.conjSp_scalarGsp, mul_one]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [coe_conjSp]
  rfl

theorem isSquare_mul_of_not_isSquare [Finite F] {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxs : ¬ IsSquare x) (hys : ¬ IsSquare y) : IsSquare (x * y) := by
  classical
  have := Fintype.ofFinite F
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hx hy), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.2 hxs, quadraticChar_neg_one_iff_not_isSquare.2 hys]
  norm_num

end CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR
