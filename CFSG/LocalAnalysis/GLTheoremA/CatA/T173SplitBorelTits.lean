module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LieType.BorelTits.OrthogonalEven
import CFSG.RankThree.PartOne.S11d.OrthModels
import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.LieType.Universal.Spin.Forms
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.SignLines
import CFSG.Assembly.QuasithinDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate116
import Certificates.Certificate119
import Certificates.Certificate122
import Certificates.Certificate123
import Certificates.Certificate2
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173S

open Module QuadraticMap CFSG.Open CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

section VanishModel

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
open scoped Matrix

private theorem exists_invariant_totallySingular_of_normalizes_aux1 {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Φ : QuadForm K (ι → K)) {R E : Subgroup (StatedOmega Φ.Q)} (hR : R ≠ ⊥)
    (hRp : IsPGroup p R) (hE : E ≤ Subgroup.normalizer (R : Set (StatedOmega Φ.Q))) :
    ∃ W : Submodule K (ι → K), W ≠ ⊥ ∧ (∀ w ∈ W, Φ.Q w = 0) ∧
      ∀ e ∈ E, ∀ w ∈ W, ((e : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W := by
  have hQ : ∀ h v, Φ.Q (natRep (StatedOmega Φ.Q) h v) = Φ.Q v := fun h v => by
    rw [natRep_apply]
    exact orthGroup_preserves Φ.Q (statedOmega_le_orthGroup Φ.Q h.2) v
  have hstar : NoQuotientReflection Φ (natRep (StatedOmega Φ.Q)) := fun h Z hZ a ha hQa => by
    simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega Φ h.2 hZ ha hQa
  have hinj : Function.Injective (natRep (StatedOmega Φ.Q)) := natRep_injective _
  refine ⟨singSeq Φ (natRep (StatedOmega Φ.Q)) R (Module.finrank K (ι → K)), ?_,
    fun w hw => isTotallySingular_singSeq Φ _ R _ w hw, fun e he w hw => ?_⟩
  · intro h0
    refine hR ((Subgroup.eq_bot_iff_forall R).mpr fun g hg => hinj ?_)
    refine LinearMap.ext fun v => ?_
    have := (le_flagKernel_singFlag p hQ hstar R hRp hg).2 (Module.finrank K (ι → K)) v
      (by rw [singFlag_finrank_succ, h0, Φ.polar.perp_bot]; trivial)
    rw [singFlag_finrank, h0, Submodule.mem_bot, sub_eq_zero] at this
    rw [this, map_one, Module.End.one_apply]
  · have := apply_mem_singSeq hQ R (Module.finrank K (ι → K)) (hE he) hw
    rwa [natRep_apply] at this

private noncomputable def exists_invariant_totallySingular_of_normalizes_aux2
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q' : QuadraticForm F (ι → F)}
    (Φ : QuadForm F (ι → F)) (hΦ : ⇑Q' = Φ.Q) (e : Q.IsometryEquiv Q') :
    ↥(orthDerived Q) ≃* StatedOmega Φ.Q :=
  (CFSG.RankThree.PartOne.orthDerivedEquiv e).trans
    (((toLinEquiv ι F).subgroupMap (StatedOmega Φ.Q)).trans
      (MulEquiv.subgroupCongr (by
        rw [statedOmega_eq_comap hΦ]
        exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι F).surjective _))).symm

private theorem exists_invariant_totallySingular_of_normalizes_aux3
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q' : QuadraticForm F (ι → F)}
    (Φ : QuadForm F (ι → F)) (hΦ : ⇑Q' = Φ.Q) (e : Q.IsometryEquiv Q')
    (g : ↥(orthDerived Q)) (v : ι → F) :
    natRep (StatedOmega Φ.Q)
        (exists_invariant_totallySingular_of_normalizes_aux2 (Q := Q) Φ hΦ e g) v =
      e.toLinearEquiv ((g : V ≃ₗ[F] V) (e.toLinearEquiv.symm v)) := by
  rw [natRep_apply]
  rw [show ((exists_invariant_totallySingular_of_normalizes_aux2 (Q := Q) Φ hΦ e g :
      StatedOmega Φ.Q) : GL ι F) = (toLinEquiv ι F).symm
        (CFSG.RankThree.PartOne.orthDerivedEquiv e g) from rfl]
  rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
  rw [show (CFSG.RankThree.PartOne.orthDerivedEquiv e g :
      (ι → F) ≃ₗ[F] (ι → F)) =
        CFSG.RankThree.PartOne.linConj e.toLinearEquiv (g : V ≃ₗ[F] V) from rfl]
  exact CFSG.RankThree.PartOne.linConj_apply e.toLinearEquiv (g : V ≃ₗ[F] V) v

private theorem exists_invariant_totallySingular_of_normalizes_aux5
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q' : QuadraticForm F (ι → F)}
    (Φ : QuadForm F (ι → F)) (hΦ : ⇑Q' = Φ.Q) (e : Q.IsometryEquiv Q')
    {X : Subgroup ↥(orthDerived Q)} {W' : Submodule F (ι → F)} (hW'0 : W' ≠ ⊥)
    (hW's : ∀ w ∈ W', Φ.Q w = 0)
    (hW'i : ∀ g ∈ X, ∀ w ∈ W',
      e.toLinearEquiv ((g : V ≃ₗ[F] V) (e.toLinearEquiv.symm w)) ∈ W') :
    ∃ W : Submodule F V, W ≠ ⊥ ∧ (∀ w ∈ W, Q w = 0) ∧
      ∀ g ∈ X, ∀ w ∈ W, (g : V ≃ₗ[F] V) w ∈ W := by
  refine ⟨W'.comap e.toLinearEquiv.toLinearMap, ?_, ?_, ?_⟩
  · intro hbot
    apply hW'0
    rw [eq_bot_iff] at hbot ⊢
    intro w hw
    have hmem : e.toLinearEquiv.symm w ∈ W'.comap e.toLinearEquiv.toLinearMap := by
      rw [Submodule.mem_comap]
      simpa using hw
    have h1 : e.toLinearEquiv.symm w = 0 := by
      have h2 := hbot hmem
      rwa [Submodule.mem_bot] at h2
    rw [Submodule.mem_bot]
    simpa using congrArg e.toLinearEquiv h1
  · intro w hw
    have h1 : Φ.Q (e w) = 0 := hW's (e w) (Submodule.mem_comap.mp hw)
    rw [← congrFun hΦ (e w), e.map_app w] at h1
    exact h1
  · intro g hg w hw
    rw [Submodule.mem_comap]
    have h1 := hW'i g hg (e w) (Submodule.mem_comap.mp hw)
    simpa using h1

private theorem exists_invariant_totallySingular_of_normalizes_aux4
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q' : QuadraticForm F (ι → F)}
    (Φ : QuadForm F (ι → F)) (hΦ : ⇑Q' = Φ.Q) (e : Q.IsometryEquiv Q')
    {X T : Subgroup ↥(orthDerived Q)} (hT2 : IsPGroup 2 T) (hT0 : T ≠ ⊥)
    (hXT : X ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q))) :
    ∃ W : Submodule F V, W ≠ ⊥ ∧ (∀ w ∈ W, Q w = 0) ∧
      ∀ g ∈ X, ∀ w ∈ W, (g : V ≃ₗ[F] V) w ∈ W := by
  classical
  let Θ : ↥(orthDerived Q) ≃* StatedOmega Φ.Q :=
    exists_invariant_totallySingular_of_normalizes_aux2 (Q := Q) Φ hΦ e
  have hΘ : ∀ g v, natRep (StatedOmega Φ.Q) (Θ g) v =
      e.toLinearEquiv ((g : V ≃ₗ[F] V) (e.toLinearEquiv.symm v)) := by
    intro g v
    change natRep (StatedOmega Φ.Q)
      (exists_invariant_totallySingular_of_normalizes_aux2 (Q := Q) Φ hΦ e g) v =
        e.toLinearEquiv ((g : V ≃ₗ[F] V) (e.toLinearEquiv.symm v))
    exact exists_invariant_totallySingular_of_normalizes_aux3 (Q := Q) Φ hΦ e g v
  have hT2' : IsPGroup 2 (T.map Θ.toMonoidHom) := hT2.map Θ.toMonoidHom
  have hT0' : T.map Θ.toMonoidHom ≠ ⊥ := fun h =>
    hT0 ((Subgroup.map_eq_bot_iff_of_injective (H := T) (f := Θ.toMonoidHom)
      (hf := fun a b hab => Θ.injective hab)).mp h)
  have hXT' : X.map Θ.toMonoidHom ≤
      Subgroup.normalizer (T.map Θ.toMonoidHom : Set (StatedOmega Φ.Q)) :=
    (Subgroup.map_mono hXT).trans (Subgroup.le_normalizer_map Θ.toMonoidHom)
  obtain ⟨W', hW'0, hW's, hW'i⟩ :=
    exists_invariant_totallySingular_of_normalizes_aux1 2 Φ hT0' hT2' hXT'
  refine exists_invariant_totallySingular_of_normalizes_aux5 (Q := Q) Φ hΦ e hW'0 hW's ?_
  intro g hg w hw
  have h1 := hW'i (Θ g) (Subgroup.mem_map_of_mem Θ.toMonoidHom hg) w hw
  rwa [← natRep_apply, hΘ g w] at h1

theorem exists_invariant_totallySingular_of_normalizes
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ} (hdim : finrank F V = 2 * l)
    (hl : 4 ≤ l) {X T : Subgroup ↥(orthDerived Q)} (hT2 : IsPGroup 2 T) (hT0 : T ≠ ⊥)
    (hXT : X ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q))) :
    ∃ W : Submodule F V, W ≠ ⊥ ∧ (∀ w ∈ W, Q w = 0) ∧
      ∀ g ∈ X, ∀ w ∈ W, (g : V ≃ₗ[F] V) w ∈ W := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ (n := l)
    (by omega) hdim with h | ⟨b, c, hirr, h⟩
  · obtain ⟨e⟩ := h
    exact exists_invariant_totallySingular_of_normalizes_aux4 (quadPlusForm l F)
      (coe_quadPlus l F) e hT2 hT0 hXT
  · obtain ⟨e⟩ := h
    exact exists_invariant_totallySingular_of_normalizes_aux4 (quadMinusForm l F b c hirr)
      (coe_quadMinus l F b c) e hT2 hT0 hXT

end VanishModel

end CFSG.LocalAnalysis.GLTheoremA.T173S

end
