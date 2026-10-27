module

public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35BlockD4
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35BlockSL
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35PlaneD4
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import CFSG.Open.GLBDefs
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.ClassicalInvolution.WeakCT.TorusAgree
import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.Walter.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT coordinateQuadPlus_fieldAut
  coordinateQuadPlus_isExtension incl incl_injective fieldAutT_fixes_J)
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (nonempty_statedProj_equiv_adjointGroup)

theorem fixedBlocks_fieldAutT_d4 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    FixedBlocks 3 (fieldAutT (coordinateQuadPlus 4 K) σ (coordinateQuadPlus_fieldAut 4 σ)) 4 := by
  let k : Subfield K := RingHom.eqLocusField (σ : K →+* K) (RingHom.id K)
  have hext := coordinateQuadPlus_isExtension k 4
  obtain ⟨β⟩ := nonempty_statedProj_equiv_adjointGroup k
  let φ : adjointGroup Tag.D4 k →* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    (incl k hext).comp (coordinatePlusWitnessEquiv k β.symm).toMonoidHom
  have hφ : Function.Injective φ :=
    (incl_injective k hext (by norm_num)).comp (coordinatePlusWitnessEquiv k β.symm).injective
  have hfix : ∀ g, fieldAutT (coordinateQuadPlus 4 K) σ (coordinateQuadPlus_fieldAut 4 σ) (φ g) =
      φ g := fun g =>
    fieldAutT_fixes_J k _ σ _ hext (fun _ => RingHom.mem_eqLocusField) ⟨_, rfl⟩
  refine fixedBlocks_of_hom φ (fun i => d4Block k i (uSL 1)) (fun i => d4Block k i WSL) ?_
    (fun i => hfix _) (fun i => hfix _) (fun i => ?_) (fun i => ?_)
  · rintro i j hij _ (rfl | rfl) _ (rfl | rfl) <;> exact d4Block_commute k hij _ _
  · simp only [← map_commutatorElement, ← map_pow, comm_uSL_WSL_pow_three, map_one]
  · rw [MonoidHom.mem_ker, ← map_one φ, hφ.eq_iff]
    simp only [← map_commutatorElement]
    rw [← map_one (d4Block k i), (d4Block_injective k i).eq_iff,
      commutatorElement_eq_one_iff_commute]
    exact not_commute_comm_uSL_WSL

theorem k35Good_of_d4 {S : Type} [Group S] [Finite S] {r f : ℕ}
    (hm : StatedClassicalModel S .POmegaPlus 4 r f) : K35Good S := by
  intro A hA hA9
  rcases exists_inner_or_fieldAutT_d4 hm hA.2 hA9 with
    hinn | ⟨hf3, α, hαA, hα1, K, _, _, ψ, σ, hK, -, hψ⟩
  · exact Or.inl hinn
  by_cases h2 : ringChar K = 2
  · haveI := ringChar.of_eq h2
    refine Or.inr (Or.inl ⟨α, hαA, hα1, (fixedBlocks_fieldAutT_d4 σ).map ψ.symm.toMonoidHom
      (fun a b hab => ψ.symm.injective hab) fun x => ?_⟩)
    simp only [MulEquiv.coe_toMonoidHom, ← hψ, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  obtain ⟨β⟩ := nonempty_statedProj_equiv_adjointGroup K
  let θ : adjointGroup Tag.D4 K ≃* S := (coordinatePlusWitnessEquiv K β.symm).trans ψ.symm
  have hK4 : 4 ≤ Nat.card K := by
    obtain ⟨⟨hr, hf, -⟩, -⟩ := hm
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr.two_le 3
      _ ≤ r ^ f := Nat.pow_le_pow_right hr.pos (Nat.le_of_dvd hf hf3)
  refine Or.inr (Or.inr ⟨θ (d4Block K 0 (-1)), by rw [← map_pow, d4Block_zero_neg_one_sq, map_one],
    fun h => d4Block_zero_neg_one_ne_one K h2 (θ.injective (h.trans (map_one θ).symm)), ?_⟩)
  refine (fixedBlocks_conj_d4Block K hK4).map θ.toMonoidHom (fun a b hab => θ.injective hab)
    fun x => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
