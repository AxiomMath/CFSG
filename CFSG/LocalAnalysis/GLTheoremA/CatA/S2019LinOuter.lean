module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Outer
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.SignalizerFunctorTheorem.NonLocal.LinearMain
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped commutatorElement

variable {n : ℕ} {F : Type} [Field F]

theorem commutator_fixSubgroup_fieldAut_le (σ : F ≃+* F) :
    ⁅fixSubgroup (fieldAut n F σ), fixSubgroup (fieldAut n F σ)⁆ ≤
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
  have hk : ∀ c, c ∈ semilinearFixedSubfield σ ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  have hfix : ∀ g : Matrix.SpecialLinearGroup (Fin n) F,
      proj n F g ∈ fixSubgroup (fieldAut n F σ) →
        ∃ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F),
          Matrix.SpecialLinearGroup.map σ.toRingHom g = g * z := by
    intro g hg
    rw [mem_fixSubgroup, fieldAut_proj, proj_eq_proj_iff] at hg
    refine ⟨((Matrix.SpecialLinearGroup.map σ.toRingHom g)⁻¹ * g)⁻¹,
      Subgroup.inv_mem _ (scalars_le_center n F hg), ?_⟩
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := proj_surjective n F x
  obtain ⟨g', rfl⟩ := proj_surjective n F y
  obtain ⟨z, hz, hgz⟩ := hfix g hx
  obtain ⟨z', hz', hgz'⟩ := hfix g' hy
  have key : Matrix.SpecialLinearGroup.map σ.toRingHom ⁅g, g'⁆ = ⁅g, g'⁆ := by
    rw [map_commutatorElement, hgz, hgz']
    exact commutatorElement_mul_mul_of_central (Subgroup.mem_center_iff.1 hz)
      (Subgroup.mem_center_iff.1 hz')
  refine mem_range_linearSubfieldInclusion.2
    ⟨⁅g, g'⁆, fun i j => (hk _).2 ?_, map_commutatorElement _ _ _⟩
  have := congrArg (fun m : Matrix.SpecialLinearGroup (Fin n) F =>
    (m : Matrix (Fin n) (Fin n) F) i j) key
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
  exact this

theorem s2019LinOuter : S2019LinOuter := by
  intro p q hp hp2 hq hq2 hqp F _ _ _ n hn β hβp hβ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite F
  haveI : Finite (Matrix.SpecialLinearGroup (Fin n) F) :=
    Finite.of_injective (fun g : Matrix.SpecialLinearGroup (Fin n) F =>
      (g : Matrix (Fin n) (Fin n) F)) Subtype.val_injective
  haveI : Finite (projectiveSL n F) := Finite.of_surjective (proj n F) (proj_surjective n F)
  obtain ⟨e, -, hcard⟩ := FiniteField.card F q
  have hβE : β ∈ semilinearAutGroup n F :=
    mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two hp2) hβp
  have hβD : β ∉ linearAutGroup n F := by
    rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rintro ⟨A, hA⟩
    exact hβ A hA.symm
  have hβ1 : β ≠ 1 := fun h1 => hβ 1 (by rw [h1, map_one])
  obtain ⟨-, σ, -, ⟨γ, -, hγ⟩, -⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hq e.pos hn (by rw [Nat.card_eq_fintype_card, hcard]) hp β hβE hβD
      (orderOf_eq_prime hβp hβ1)
  rw [hγ]
  have hk : ∀ c ∈ semilinearFixedSubfield σ, σ c = c := fun c hc => RingHom.mem_eqLocusField.1 hc
  refine s2019FixCentralizes_conj_of_nonLocalized p (fieldAut n F σ) γ ?_
    (commutator_fixSubgroup_fieldAut_le σ)
    (simple_nonabelian_range_linearSubfieldInclusion hn _).1
    (CFSG.SignalizerFunctorTheorem.NonLocal.nonLocalized_linearSubfield hn _)
  rintro _ ⟨x, rfl⟩
  exact fieldAut_linearSubfieldInclusion hk x

end CFSG.LocalAnalysis.GLTheoremA.S2019
