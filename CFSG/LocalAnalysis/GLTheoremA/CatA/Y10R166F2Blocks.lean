module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75Z1
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
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
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Matrix CFSG.RankThree.PartTwo.Census CFSG.Open
open scoped commutatorElement

local notation "𝔽₂" => ZMod 2

namespace F2Block

theorem threeCycleMat_symm : (threeCycleMat 𝔽₂).transpose = threeCycleMat 𝔽₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [threeCycleMat]

theorem threeCycleMat_mulVec_eq_self {v : Fin 2 → 𝔽₂}
    (h : threeCycleMat 𝔽₂ *ᵥ v = v) : v = 0 := by
  have h0 : v 1 = v 0 := by
    simpa [threeCycleMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0
  have h1 : v 0 + v 1 = v 1 := by
    simpa [threeCycleMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 1
  have hv0 : v 0 = 0 := by
    have h2 : v 0 + v 1 = 0 + v 1 := by rw [zero_add]; exact h1
    exact add_right_cancel h2
  have hv1 : v 1 = 0 := by rw [h0, hv0]
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

theorem threeCycleMat_commute_cases (A : Matrix (Fin 2) (Fin 2) 𝔽₂)
    (h : A * threeCycleMat 𝔽₂ = threeCycleMat 𝔽₂ * A) :
    A = 0 ∨ A = 1 ∨ A = threeCycleMat 𝔽₂ ∨ A = threeCycleMat 𝔽₂ ^ 2 := by
  have h01 : A 0 1 = A 1 0 := by
    have := congrFun (congrFun h 0) 0
    simpa [threeCycleMat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : A 0 0 + A 0 1 = A 1 1 := by
    have := congrFun (congrFun h 0) 1
    simpa [threeCycleMat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hA : A = !![A 0 0, A 0 1; A 0 1, A 0 0 + A 0 1] := by
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · simpa using h01
    · simpa using h01.symm
    · simpa using h10.symm
  have h2 : ∀ x : 𝔽₂, x = 0 ∨ x = 1 := by decide
  have key : ∀ a b : 𝔽₂,
      (!![a, b; b, a + b] : Matrix (Fin 2) (Fin 2) 𝔽₂) = 0 ∨
        (!![a, b; b, a + b] : Matrix (Fin 2) (Fin 2) 𝔽₂) = 1 ∨
        (!![a, b; b, a + b] : Matrix (Fin 2) (Fin 2) 𝔽₂) = threeCycleMat 𝔽₂ ∨
        (!![a, b; b, a + b] : Matrix (Fin 2) (Fin 2) 𝔽₂) = threeCycleMat 𝔽₂ ^ 2 := by
    intro a b
    rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl
    · left; ext i j; fin_cases i <;> fin_cases j <;> simp <;> decide
    · right; right; left; ext i j; fin_cases i <;> fin_cases j <;> simp [threeCycleMat] <;>
        decide
    · right; left; ext i j; fin_cases i <;> fin_cases j <;> simp <;> decide
    · right; right; right; ext i j; fin_cases i <;> fin_cases j <;>
        simp [threeCycleMat_sq] <;> decide
  rw [hA]
  exact key (A 0 0) (A 0 1)

section GenericBlock

variable {Q : Type} [Fintype Q] [DecidableEq Q]

@[expose] def xBlockMat : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂ :=
  fromBlocks (threeCycleMat 𝔽₂) 0 0 1

theorem det_xBlockMat : xBlockMat (Q := Q).det = 1 := by
  rw [xBlockMat, Matrix.det_fromBlocks_zero₂₁, det_threeCycleMat, Matrix.det_one, mul_one]

@[expose] def xBlock : Matrix.SpecialLinearGroup (Fin 2 ⊕ Q) 𝔽₂ :=
  ⟨xBlockMat (Q := Q), det_xBlockMat⟩

@[expose] def jBlockHom : Matrix.SpecialLinearGroup Q 𝔽₂ →* Matrix.SpecialLinearGroup (Fin 2 ⊕ Q) 𝔽₂ where
  toFun A := ⟨fromBlocks 1 0 0 (A : Matrix Q Q 𝔽₂), by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, A.2]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    change fromBlocks 1 0 0 ((A : Matrix Q Q 𝔽₂) * (B : Matrix Q Q 𝔽₂)) =
      fromBlocks 1 0 0 (A : Matrix Q Q 𝔽₂) * fromBlocks 1 0 0 (B : Matrix Q Q 𝔽₂)
    rw [Matrix.fromBlocks_multiply]
    simp)

theorem coe_xBlock : (xBlock (Q := Q) : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) =
    fromBlocks (threeCycleMat 𝔽₂) 0 0 1 := rfl

theorem coe_jBlockHom (A : Matrix.SpecialLinearGroup Q 𝔽₂) :
    ((jBlockHom (Q := Q) A : Matrix.SpecialLinearGroup (Fin 2 ⊕ Q) 𝔽₂) :
      Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) = fromBlocks 1 0 0 (A : Matrix Q Q 𝔽₂) := rfl

theorem jBlockHom_injective {Q : Type} [Fintype Q] [DecidableEq Q] :
    Function.Injective (jBlockHom (Q := Q)) := by
  intro A B h
  apply Subtype.ext
  have h1 : (jBlockHom (Q := Q) A : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) =
      (jBlockHom (Q := Q) B : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) := congrArg Subtype.val h
  change fromBlocks 1 0 0 (A : Matrix Q Q 𝔽₂) =
    fromBlocks 1 0 0 (B : Matrix Q Q 𝔽₂) at h1
  obtain ⟨-, -, -, hAB⟩ := Matrix.fromBlocks_inj.1 h1
  exact hAB

theorem centralizer_xBlock_le (g : Matrix.SpecialLinearGroup (Fin 2 ⊕ Q) 𝔽₂)
    (hg : g ∈ Subgroup.centralizer ({xBlock (Q := Q)} : Set _)) :
    g ∈ (jBlockHom (Q := Q)).range ⊔ Subgroup.zpowers (xBlock (Q := Q)) := by
  have hcomm : g * xBlock (Q := Q) = xBlock (Q := Q) * g :=
    Subgroup.mem_centralizer_singleton_iff.1 hg
  have hmat : (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) *
      (xBlock (Q := Q) : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) =
      (xBlock (Q := Q) : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) *
        (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) := by
    simpa using congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2 ⊕ Q) 𝔽₂ =>
      (z : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂)) hcomm
  set A : Matrix (Fin 2) (Fin 2) 𝔽₂ := fun i j =>
    (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) (Sum.inl i) (Sum.inl j)
  set B : Matrix (Fin 2) Q 𝔽₂ := fun i q =>
    (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) (Sum.inl i) (Sum.inr q)
  set C' : Matrix Q (Fin 2) 𝔽₂ := fun q j =>
    (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) (Sum.inr q) (Sum.inl j)
  set D : Matrix Q Q 𝔽₂ := fun q q' =>
    (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) (Sum.inr q) (Sum.inr q')
  have hgdec : (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) = fromBlocks A B C' D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hxdec : (xBlock (Q := Q) : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) =
      fromBlocks (threeCycleMat 𝔽₂) 0 0 1 := rfl
  rw [hgdec, hxdec, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hmat
  obtain ⟨hAC, hCB, hC'C, -⟩ := Matrix.fromBlocks_inj.1 hmat
  have hAC' : A * threeCycleMat 𝔽₂ = threeCycleMat 𝔽₂ * A := by
    have h1 : B * (0 : Matrix Q (Fin 2) 𝔽₂) = 0 := Matrix.mul_zero B
    have h2 : (0 : Matrix (Fin 2) Q 𝔽₂) * C' = 0 := Matrix.zero_mul C'
    simpa [h1, h2] using hAC
  have hCB'' : B = threeCycleMat 𝔽₂ * B := by
    have h1 : A * (0 : Matrix (Fin 2) Q 𝔽₂) = 0 := Matrix.mul_zero A
    have h2 : (0 : Matrix Q Q 𝔽₂) * D = 0 := Matrix.zero_mul D
    have h3 : B * (1 : Matrix Q Q 𝔽₂) = B := Matrix.mul_one B
    simpa [h1, h2, h3] using hCB
  have hCB' : threeCycleMat 𝔽₂ * B = B := hCB''.symm
  have hC'C' : C' * threeCycleMat 𝔽₂ = C' := by
    have h1 : D * (0 : Matrix Q (Fin 2) 𝔽₂) = 0 := Matrix.mul_zero D
    have h2 : (0 : Matrix Q (Fin 2) 𝔽₂) * A = 0 := Matrix.zero_mul A
    have h3 : (1 : Matrix Q Q 𝔽₂) * C' = C' := Matrix.one_mul C'
    simpa [h1, h2, h3] using hC'C
  have hB : B = 0 := by
    ext i q
    have hcol : (fun i => B i q) = 0 := by
      apply threeCycleMat_mulVec_eq_self
      ext i
      simpa [Matrix.mulVec, Matrix.mul_apply] using congrFun (congrFun hCB' i) q
    exact congrFun hcol i
  have hC' : C' = 0 := by
    ext q j
    have hrow : (fun i => C' q i) = 0 := by
      apply threeCycleMat_mulVec_eq_self
      ext j
      calc (threeCycleMat 𝔽₂ *ᵥ fun i => C' q i) j
          = ∑ i, threeCycleMat 𝔽₂ j i * C' q i := rfl
        _ = ∑ i, C' q i * threeCycleMat 𝔽₂ i j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hsymm : threeCycleMat 𝔽₂ j i = threeCycleMat 𝔽₂ i j := by
              have := congrFun (congrFun threeCycleMat_symm i) j
              simpa using this
            rw [hsymm]
            ring
        _ = (C' * threeCycleMat 𝔽₂) q j := by rw [Matrix.mul_apply]
        _ = C' q j := by rw [hC'C']
    exact congrFun hrow j
  have hAcases := threeCycleMat_commute_cases A hAC'
  have hg' : (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) = fromBlocks A 0 0 D := by
    simpa [hB, hC'] using hgdec
  have hdet : A.det * D.det = 1 := by
    have := g.2
    rw [hg', Matrix.det_fromBlocks_zero₂₁] at this
    simpa using this
  have hAne : A ≠ 0 := by
    intro hA0
    rw [hA0, Matrix.det_zero] at hdet
    have : (0 : 𝔽₂) * D.det = 1 := hdet
    simpa using this
  have hAcases' : A = 1 ∨ A = threeCycleMat 𝔽₂ ∨ A = threeCycleMat 𝔽₂ ^ 2 := by
    rcases hAcases with h0 | h1 | h2 | h3
    · exact absurd h0 hAne
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
  have hDdet : D.det = 1 := by
    rcases hAcases' with h1 | h2 | h3
    · rw [h1, Matrix.det_one, one_mul] at hdet; exact hdet
    · rw [h2, det_threeCycleMat, one_mul] at hdet; exact hdet
    · rw [h3, Matrix.det_pow, det_threeCycleMat, one_pow, one_mul] at hdet; exact hdet
  let Dj : Matrix.SpecialLinearGroup Q 𝔽₂ := ⟨D, hDdet⟩
  have hJ : jBlockHom Dj ∈ (jBlockHom (Q := Q)).range := ⟨Dj, rfl⟩
  have hJle : jBlockHom Dj ∈ (jBlockHom (Q := Q)).range ⊔ Subgroup.zpowers (xBlock (Q := Q)) :=
    Subgroup.mem_sup_left hJ
  rcases hAcases' with h1 | h2 | h3
  · have hg1 : g = jBlockHom Dj := by
      apply Subtype.ext
      rw [hg', h1, coe_jBlockHom]
    rw [hg1]; exact Subgroup.mem_sup_left hJ
  · have hg1 : g = jBlockHom Dj * xBlock (Q := Q) := by
      apply Subtype.ext
      change (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) =
        (jBlockHom Dj : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) *
          (xBlock (Q := Q) : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂)
      rw [hg', h2, coe_jBlockHom, coe_xBlock, Matrix.fromBlocks_multiply]
      simp
      rfl
    rw [hg1]
    exact Subgroup.mul_mem_sup hJ (Subgroup.mem_zpowers _)
  · have hx2 : ((xBlock (Q := Q)) ^ 2 : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) =
        fromBlocks (threeCycleMat 𝔽₂ ^ 2) 0 0 1 := by
      rw [pow_two]
      change (xBlock (Q := Q) : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) *
        (xBlock (Q := Q) : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) = _
      rw [coe_xBlock, Matrix.fromBlocks_multiply]
      simp [pow_two]
    have hg1 : g = jBlockHom Dj * xBlock (Q := Q) ^ 2 := by
      apply Subtype.ext
      change (g : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) =
        (jBlockHom Dj : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂) *
          ((xBlock (Q := Q)) ^ 2 : Matrix (Fin 2 ⊕ Q) (Fin 2 ⊕ Q) 𝔽₂)
      rw [hg', h3, coe_jBlockHom, hx2, Matrix.fromBlocks_multiply]
      simp
      rfl
    rw [hg1]
    exact Subgroup.mul_mem_sup hJ
        (Subgroup.zpow_mem_zpowers (xBlock (Q := Q)) 2)

end GenericBlock

end F2Block

namespace SLNineTwo

open F2Block

abbrev Ix := Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 1)))

abbrev cMat : Matrix (Fin 2) (Fin 2) 𝔽₂ := threeCycleMat 𝔽₂

@[expose] def bMat (a : Fin 4 → ZMod 3) : Matrix Ix Ix 𝔽₂ :=
  fromBlocks (cMat ^ (a 0).val) 0 0
    (fromBlocks (cMat ^ (a 1).val) 0 0
      (fromBlocks (cMat ^ (a 2).val) 0 0
        (fromBlocks (cMat ^ (a 3).val) 0 0 (1 : Matrix (Fin 1) (Fin 1) 𝔽₂))))

private theorem bMat_add (a a' : Fin 4 → ZMod 3) :
    bMat (a + a') = bMat a * bMat a' := by
  simp only [bMat, Pi.add_apply, threeCycleMat_pow_val_add, fromBlocks_multiply]
  simp

theorem det_bMat (a : Fin 4 → ZMod 3) : (bMat a).det = 1 := by
  rw [bMat, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁,
    det_fromBlocks_zero₂₁]
  simp [det_pow, det_threeCycleMat]

@[expose] def bHom : Multiplicative (Fin 4 → ZMod 3) →* Matrix.SpecialLinearGroup Ix 𝔽₂ where
  toFun a := ⟨bMat a.toAdd, det_bMat a.toAdd⟩
  map_one' := by
    apply Subtype.ext
    change bMat 0 = 1
    rw [bMat]
    simp
  map_mul' a b := by
    apply Subtype.ext
    change bMat (a.toAdd + b.toAdd) = bMat a.toAdd * bMat b.toAdd
    rw [bMat_add]

def B : Subgroup (Matrix.SpecialLinearGroup Ix 𝔽₂) := bHom.range

theorem threeCycleMat_pow_val_injective {x y : ZMod 3}
    (h : cMat ^ x.val = cMat ^ y.val) : x = y := by
  fin_cases x <;> fin_cases y <;> first | rfl | (exfalso; revert h; decide)

private theorem bHom_injective : Function.Injective bHom := by
  intro a b hab
  have h1 : bMat a.toAdd = bMat b.toAdd := congrArg Subtype.val hab
  have hk : ∀ k : Fin 4, a.toAdd k = b.toAdd k := by
    intro k
    apply threeCycleMat_pow_val_injective
    fin_cases k
    · ext i j
      have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl j)
      simpa [bMat, fromBlocks_apply₁₁] using this
    · ext i j
      have := congrFun (congrFun h1 (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inl j))
      simpa [bMat, fromBlocks_apply₂₂, fromBlocks_apply₁₁] using this
    · ext i j
      have := congrFun (congrFun h1 (Sum.inr (Sum.inr (Sum.inl i))))
        (Sum.inr (Sum.inr (Sum.inl j)))
      simpa [bMat, fromBlocks_apply₂₂, fromBlocks_apply₁₁] using this
    · ext i j
      have := congrFun (congrFun h1 (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
      simpa [bMat, fromBlocks_apply₂₂, fromBlocks_apply₁₁] using this
  exact Multiplicative.toAdd.injective (funext hk)

private theorem pow_three_multiplicative_pi (u : Multiplicative (Fin 4 → ZMod 3)) : u ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext k
  show (3 : ℕ) • u.toAdd k = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem isElemAbelian_B : IsElemAbelian 3 B :=
  isElemAbelian_range (p := 3) pow_three_multiplicative_pi bHom

def xElt : Matrix.SpecialLinearGroup Ix 𝔽₂ :=
  bHom (Multiplicative.ofAdd (Pi.single (0 : Fin 4) (1 : ZMod 3)))

private theorem xElt_mem_B : xElt ∈ B := ⟨_, rfl⟩

theorem xElt_ne_one : xElt ≠ 1 := by
  intro h
  have h1 : Multiplicative.ofAdd (Pi.single (0 : Fin 4) (1 : ZMod 3)) = 1 :=
    bHom_injective (by simpa [xElt] using h)
  have h2 := congrFun (Multiplicative.toAdd.injective h1) 0
  simp at h2

theorem xElt_pow_three : xElt ^ 3 = 1 := by
  exact isElemAbelian_B.2 xElt xElt_mem_B

abbrev W7 := Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 1))

abbrev W5 := Fin 2 ⊕ (Fin 2 ⊕ Fin 1)

abbrev W3 := Fin 2 ⊕ Fin 1

@[expose] def jHom : Matrix.SpecialLinearGroup W7 𝔽₂ →*
    Matrix.SpecialLinearGroup Ix 𝔽₂ :=
  jBlockHom (Q := W7)

@[expose] def jHom5 : Matrix.SpecialLinearGroup W5 𝔽₂ →* Matrix.SpecialLinearGroup W7 𝔽₂ :=
  jBlockHom (Q := W5)

private theorem zmod3_val_one : ((1 : ZMod 3)).val = 1 := by decide

@[expose] def jHom3 : Matrix.SpecialLinearGroup W3 𝔽₂ →* Matrix.SpecialLinearGroup W5 𝔽₂ :=
  jBlockHom (Q := W3)

@[expose] def J : Subgroup (Matrix.SpecialLinearGroup Ix 𝔽₂) := jHom.range

@[expose] def b2W : Matrix.SpecialLinearGroup W7 𝔽₂ := xBlock (Q := W5)

@[expose] def b3W : Matrix.SpecialLinearGroup W7 𝔽₂ := jHom5 (xBlock (Q := W3))

private theorem xElt_eq_xBlock : xElt = xBlock (Q := W7) := by
  apply Subtype.ext
  change bMat (Pi.single (0 : Fin 4) (1 : ZMod 3)) = xBlockMat (Q := W7)
  simp [bMat, xBlockMat, Pi.single_eq_same, fromBlocks_one]
  rw [zmod3_val_one, pow_one]

@[expose] def bMatW (a : Fin 3 → ZMod 3) : Matrix W7 W7 𝔽₂ :=
  fromBlocks (cMat ^ (a 0).val) 0 0
    (fromBlocks (cMat ^ (a 1).val) 0 0
      (fromBlocks (cMat ^ (a 2).val) 0 0 (1 : Matrix (Fin 1) (Fin 1) 𝔽₂)))

theorem det_bMatW (a : Fin 3 → ZMod 3) : (bMatW a).det = 1 := by
  rw [bMatW, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
  simp [det_pow, det_threeCycleMat]

@[expose] def bHomW : Multiplicative (Fin 3 → ZMod 3) →* Matrix.SpecialLinearGroup W7 𝔽₂ where
  toFun a := ⟨bMatW a.toAdd, det_bMatW a.toAdd⟩
  map_one' := by
    apply Subtype.ext
    change bMatW 0 = 1
    simp [bMatW]
  map_mul' a b := by
    apply Subtype.ext
    change bMatW (a.toAdd + b.toAdd) = bMatW a.toAdd * bMatW b.toAdd
    simp only [bMatW, Pi.add_apply, threeCycleMat_pow_val_add, fromBlocks_multiply]
    simp

theorem J_le_centralizer_xElt : J ≤ Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change (jBlockHom (Q := W7) A : Matrix Ix Ix 𝔽₂) * (xElt : Matrix Ix Ix 𝔽₂) =
    (xElt : Matrix Ix Ix 𝔽₂) * (jBlockHom (Q := W7) A : Matrix Ix Ix 𝔽₂)
  rw [xElt_eq_xBlock, coe_jBlockHom, coe_xBlock, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

theorem centralizer_xElt_le_sup :
    Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂)) ≤
      J ⊔ Subgroup.zpowers xElt := by
  intro g hg
  have h := centralizer_xBlock_le (Q := W7) g (by simpa [xElt_eq_xBlock] using hg)
  simpa [J, jHom, xElt_eq_xBlock] using h

private theorem xElt_mem_centralizer :
    xElt ∈ Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]

private theorem centralizer_xElt_eq_sup :
    Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂)) =
      J ⊔ Subgroup.zpowers xElt := by
  refine le_antisymm centralizer_xElt_le_sup ?_
  refine sup_le J_le_centralizer_xElt ?_
  rw [Subgroup.zpowers_le]
  exact xElt_mem_centralizer

theorem commutator_le_J :
    ⁅Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂)),
      Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂))⁆ ≤ J :=
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.commutator_le_of_sup_central
    J_le_centralizer_xElt centralizer_xElt_eq_sup
    (fun z hz m hm => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hc : Commute xElt m := (Subgroup.mem_centralizer_singleton_iff.mp hm).symm
      exact (hc.zpow_left n).eq)

theorem commutator_mem_J {g h : Matrix.SpecialLinearGroup Ix 𝔽₂}
    (hg : g ∈ Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂)))
    (hh : h ∈ Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂))) :
    g * h * g⁻¹ * h⁻¹ ∈ J := by
  have hmem : ⁅g, h⁆ ∈ ⁅Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂)),
      Subgroup.centralizer ({xElt} : Set (Matrix.SpecialLinearGroup Ix 𝔽₂))⁆ :=
    Subgroup.commutator_mem_commutator hg hh
  exact commutator_le_J hmem

theorem jHom5_injective : Function.Injective jHom5 := jBlockHom_injective

theorem jHom3_injective : Function.Injective jHom3 := jBlockHom_injective

theorem jHom_injective : Function.Injective jHom := by
  intro A B h
  apply Subtype.ext
  have h1 : (jHom A : Matrix Ix Ix 𝔽₂) = (jHom B : Matrix Ix Ix 𝔽₂) := congrArg Subtype.val h
  change fromBlocks 1 0 0 (A : Matrix W7 W7 𝔽₂) =
    fromBlocks 1 0 0 (B : Matrix W7 W7 𝔽₂) at h1
  obtain ⟨-, -, -, hAB⟩ := Matrix.fromBlocks_inj.1 h1
  exact hAB

end SLNineTwo

end CFSG.LocalAnalysis.GLTheoremA.Y10F
