module

public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.Quasithin.Background.SmithB45SzNat
public import CFSG.CGT.PushingUpLit.SolKNA.SzWeightDef
import all CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.SmithB42Sp4Real
public import Certificates.Certificate8026Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.Blueprint Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.B45Sz

@[expose] noncomputable def szEquiv (a : ℕ) : ↥(suzukiGroup a (F a)) ≃* ↥(Sz a) :=
  (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (F a))).trans
    (CFSG.ShultStronglyClosedTI.glaSzCanonicalEquivNative a)

theorem coe_szEquiv (a : ℕ) (h : ↥(suzukiGroup a (F a))) :
    (((szEquiv a h : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      ((((h⁻¹ : ↥(suzukiGroup a (F a))) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)))ᵀ := by
  have h1 : ((szEquiv a h : ↥(Sz a)) : GL (Fin 4) (F a)) =
      Matrix.GeneralLinearGroup.inverseTranspose (h : GL (Fin 4) (F a)) := by
    unfold szEquiv CFSG.ShultStronglyClosedTI.glaSzCanonicalEquivNative
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
    exact (MulEquiv.subgroupCongr_apply
        (CFSG.ShultStronglyClosedTI.map_inverseTranspose_glaSzGroup a) _).trans
      ((MulEquiv.coe_subgroupMap_apply _ _ _).trans
        (congrArg _ (MulEquiv.subgroupCongr_apply _ h)))
  rw [h1, Matrix.GeneralLinearGroup.coe_inverseTranspose]
  rfl

theorem exteriorSquareJ_mul_self (K : Type) [Field K] :
    CFSG.LinearAlgebra.exteriorSquareJ K * CFSG.LinearAlgebra.exteriorSquareJ K = 1 := by
  rw [CFSG.LinearAlgebra.exteriorSquareJ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem szEquiv_mul_J (a : ℕ) (h : ↥(suzukiGroup a (F a))) :
    (((szEquiv a h : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) *
        CFSG.LinearAlgebra.exteriorSquareJ (F a) =
      CFSG.LinearAlgebra.exteriorSquareJ (F a) *
        ((h : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) := by
  have : Fintype (F a) := Fintype.ofFinite _
  have hcard : Nat.card (F a) = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  have hJ : ((h : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a))ᵀ *
      CFSG.LinearAlgebra.exteriorSquareJ (F a) *
        ((h : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      CFSG.LinearAlgebra.exteriorSquareJ (F a) := (szIncl hcard h).2
  have hHH : ((h : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) *
      (((h⁻¹ : ↥(suzukiGroup a (F a))) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
        1 := by
    simp
  rw [coe_szEquiv]
  have h2 : ((((h⁻¹ : ↥(suzukiGroup a (F a))) : GL (Fin 4) (F a)) :
      Matrix (Fin 4) (Fin 4) (F a)))ᵀ *
      ((h : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hHH, Matrix.transpose_one]
  calc ((((h⁻¹ : ↥(suzukiGroup a (F a))) : GL (Fin 4) (F a)) :
        Matrix (Fin 4) (Fin 4) (F a)))ᵀ * CFSG.LinearAlgebra.exteriorSquareJ (F a)
      = ((((h⁻¹ : ↥(suzukiGroup a (F a))) : GL (Fin 4) (F a)) :
        Matrix (Fin 4) (Fin 4) (F a)))ᵀ * (((h : GL (Fin 4) (F a)) :
          Matrix (Fin 4) (Fin 4) (F a))ᵀ * CFSG.LinearAlgebra.exteriorSquareJ (F a) *
            ((h : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a))) := by rw [hJ]
    _ = ((((h⁻¹ : ↥(suzukiGroup a (F a))) : GL (Fin 4) (F a)) :
        Matrix (Fin 4) (Fin 4) (F a)))ᵀ * ((h : GL (Fin 4) (F a)) :
          Matrix (Fin 4) (Fin 4) (F a))ᵀ * CFSG.LinearAlgebra.exteriorSquareJ (F a) *
            ((h : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) := by
      simp only [Matrix.mul_assoc]
    _ = CFSG.LinearAlgebra.exteriorSquareJ (F a) *
        ((h : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) := by rw [h2, Matrix.one_mul]

@[expose] noncomputable def repToHom {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) : G →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.toHomUnits

theorem repOfG_repToHom {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g : G) : repOfG (repToHom ρ) g = ρ g := rfl

theorem isIrreducible_repToHom_comp {a : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) ↥(Sz a) V) (hnt : Nontrivial V)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    (repOfG (repToHom (ρ.comp (szEquiv a).toMonoidHom))).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨hnt, fun U hU => hirr U fun g w hw => ?_⟩
  have := hU ((szEquiv a).symm g) w hw
  simpa [repOfG_repToHom] using this

end CFSG.CGT.PushingUpLit.SolKNA
