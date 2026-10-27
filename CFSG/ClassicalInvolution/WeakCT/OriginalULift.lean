module

public import CFSG.LocalAnalysis.StandardType.GGActualQuadraticField
public import CFSG.LocalAnalysis.StandardType.GGFinModelCorner
public import CFSG.LieType.Steinberg.Minuscule.E6TorusLang
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Levi
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Frame
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryEmbed
public import CFSG.RankThree.PartOne.KE6.EqpOpp
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6AdjointA2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Char
public import CFSG.LocalAnalysis.StandardType.GGFinModelTorusMem
public import CFSG.ClassicalInvolution.WeakCT.FiniteModelSquareConnection
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.RankThree.CentralLift.ClassicalCoverTools
public import CFSG.Timmesfeld.RankTwo.SimplyLaced
public import CFSG.GH74.Generic.BProg.B2.GenLocL3NFAux
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Adjugate
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public noncomputable section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E
open scoped MatrixGroups

theorem ggIota_twistedE6_injective (n f : ℕ) (hf : 1 ≤ f) :
    Function.Injective (ggIota .twistedE6 n f hf) := by
  intro x y hxy
  apply (ggKbEquivTwE6 n f hf).injective
  apply Subtype.ext
  exact baseChangeGL_injective (ggRatEmb (2 * f)) hxy

theorem ggIotaK_twistedE6_ker_eq_center (n f : ℕ) (hf : 1 ≤ f) :
    (ggIotaK .twistedE6 n f hf).ker = Subgroup.center ((ggU .twistedE6 n f).K) := by
  rw [ggIotaK, ← MonoidHom.comap_ker (g := ggIota .twistedE6 n f hf)
    (f := QuotientGroup.mk' (Subgroup.center (ggU .twistedE6 n f).K)),
    (MonoidHom.ker_eq_bot_iff (ggIota .twistedE6 n f hf)).2
      (ggIota_twistedE6_injective n f hf),
    MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem algebraic_lift_unique_of_isogeny_eq
    {f : ℕ} [NeZero f]
    {lam' mu : SL(3, actualQuadraticSubfield f) →* e6Data_valid.minGroup GGL}
    (h : ∀ A, e6IsogenyAlgebraic (lam' A) = e6IsogenyAlgebraic (mu A)) :
    lam' = mu := by
  classical
  letI : Group.IsPerfect (SL(3, actualQuadraticSubfield f)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  refine CFSG.ClassicalInvolution.ModelFacts.OrthAut.eq_of_inv_mul_mem_center mu lam' ?_
  intro A
  rw [← ker_e6IsogenyAlgebraic_eq_center]
  rw [MonoidHom.mem_ker, map_mul, map_inv, h A, inv_mul_cancel]

section DonorFrame
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.RankThree.PartOne.KF4

theorem exists_e6Sl3_adjoint_frame_actualQuadraticSubfield_both {f : ℕ} [NeZero f] :
    ∃ (Ψ : SL(3, actualQuadraticSubfield f) →*
        e6Data_valid.minGroup (actualQuadraticSubfield f))
      (ρ : SL(3, actualQuadraticSubfield f) →*
        adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)),
      Function.Injective Ψ ∧ Function.Injective ρ ∧
      ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ ∧
      IsA2Frame ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ)
        (fun i j => chainRoot chain13 i j) ∧
      ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ) =
        e6rhoA2₁ (actualQuadraticSubfield f) ∧
      ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ).comp
          (blk (actualQuadraticSubfield f) 0) =
        rootSL2 Tag.E6 (actualQuadraticSubfield f) (Pi.single 0 1) ∧
      ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ).comp
          (blk (actualQuadraticSubfield f) 1) =
        rootSL2 Tag.E6 (actualQuadraticSubfield f) (Pi.single 2 1) := by
  exact CFSG.ClassicalInvolution.WeakCT.exists_e6Sl3_adjoint_frame
    (k := actualQuadraticSubfield f)

theorem exists_e6Sl3_adjoint_frame_at_a2_pair
    {f : ℕ} [NeZero f] {α β : Fin Tag.E6.rank → ℤ} (hpair : IsA2Pair α β) :
    ∃ (w : WeylGroup Tag.E6)
      (Ψ : SL(3, actualQuadraticSubfield f) →*
        e6Data_valid.minGroup (actualQuadraticSubfield f))
      (ρ : SL(3, actualQuadraticSubfield f) →*
        adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)),
      Function.Injective Ψ ∧ Function.Injective ρ ∧
      ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ ∧
      IsA2Frame ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ)
        (fun i j => w • chainRoot chain13 i j) ∧
      w • chainRoot chain13 0 1 = α ∧ w • chainRoot chain13 1 2 = β ∧
      ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ).comp
        (blk (actualQuadraticSubfield f) 0) = rootSL2 Tag.E6 (actualQuadraticSubfield f) α ∧
      ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ).comp
        (blk (actualQuadraticSubfield f) 1) = rootSL2 Tag.E6 (actualQuadraticSubfield f) β := by
  obtain ⟨w, hwα, hwβ⟩ := exists_weyl_a2Pair_E6 hpair
  obtain ⟨Ψ, ρ, hΨ, hρinj, hρ, hframe, _heq, hblk0, hblk1⟩ :=
    exists_e6Sl3_adjoint_frame_actualQuadraticSubfield_both (f := f)
  let nw : adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f) :=
    ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) (actualQuadraticSubfield f) w,
      canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) (actualQuadraticSubfield f) w⟩
  obtain ⟨c, hc⟩ := e6IsogenyT_surjective (k := actualQuadraticSubfield f) nw
  let Ψ' := (MulAut.conj c).toMonoidHom.comp Ψ
  let ρ' := (MulAut.conj nw).toMonoidHom.comp ρ
  have hρ' : ρ' = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ' := by
    apply MonoidHom.ext
    intro A
    change nw * ρ A * nw⁻¹ = e6IsogenyT (actualQuadraticSubfield f) (c * Ψ A * c⁻¹)
    rw [map_mul, map_mul, map_inv, hc]
    exact congrArg (fun y => nw * y * nw⁻¹) (DFunLike.congr_fun hρ A)
  have hJ : (adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ' =
      (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) (actualQuadraticSubfield f) w)).toMonoidHom.comp
        ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ) := by
    apply MonoidHom.ext
    intro A
    rfl
  refine ⟨w, Ψ', ρ', (MulAut.conj c).injective.comp hΨ,
    (MulAut.conj nw).injective.comp hρinj, hρ', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ]
    exact hframe.transport w
  · rw [chainRoot13_zero_one]
    exact hwα
  · rw [chainRoot13_one_two]
    exact hwβ
  · rw [hJ, MonoidHom.comp_assoc, hblk0]
    apply MonoidHom.ext
    intro A
    exact (conj_rootSL2_two w (isRoot_single Tag.E6 0) A).trans
      (congrArg (fun γ => rootSL2 Tag.E6 (actualQuadraticSubfield f) γ A) hwα)
  · rw [hJ, MonoidHom.comp_assoc, hblk1]
    apply MonoidHom.ext
    intro A
    exact (conj_rootSL2_two w (isRoot_single Tag.E6 2) A).trans
      (congrArg (fun γ => rootSL2 Tag.E6 (actualQuadraticSubfield f) γ A) hwβ)

end DonorFrame

section ActualInverseTransposeActor
open CFSG.Timmesfeld Matrix

variable {F : Type} [Field F]

private lemma transpose_mul' {N : ℕ} {K : Type} [Field K]
    (A B : Matrix.SpecialLinearGroup (Fin N) K) :
    Matrix.SpecialLinearGroup.transpose (A * B) =
      Matrix.SpecialLinearGroup.transpose B * Matrix.SpecialLinearGroup.transpose A := by
  apply Subtype.ext
  change ((A : Matrix (Fin N) (Fin N) K) * (B : Matrix (Fin N) (Fin N) K))ᵀ =
    (B : Matrix (Fin N) (Fin N) K)ᵀ * (A : Matrix (Fin N) (Fin N) K)ᵀ
  rw [Matrix.transpose_mul]

private lemma transpose_one' {N : ℕ} {K : Type} [Field K] :
    Matrix.SpecialLinearGroup.transpose (1 : Matrix.SpecialLinearGroup (Fin N) K) = 1 := by
  apply Subtype.ext
  change ((1 : Matrix (Fin N) (Fin N) K))ᵀ = 1
  rw [Matrix.transpose_one]

private lemma transpose_inv' {N : ℕ} {K : Type} [Field K]
    (A : Matrix.SpecialLinearGroup (Fin N) K) :
    Matrix.SpecialLinearGroup.transpose A⁻¹ =
      (Matrix.SpecialLinearGroup.transpose A)⁻¹ := by
  have h : Matrix.SpecialLinearGroup.transpose A *
      Matrix.SpecialLinearGroup.transpose A⁻¹ = 1 := by
    rw [← transpose_mul', inv_mul_cancel, transpose_one']
  exact eq_inv_of_mul_eq_one_right h

private lemma transpose_transpose' {N : ℕ} {K : Type} [Field K]
    (A : Matrix.SpecialLinearGroup (Fin N) K) :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose A) = A := by
  apply Subtype.ext
  change ((A : Matrix (Fin N) (Fin N) K)ᵀ)ᵀ = (A : Matrix (Fin N) (Fin N) K)
  rw [Matrix.transpose_transpose]

@[expose] noncomputable def inverseTransposeSL (N : ℕ) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin N) K ≃* Matrix.SpecialLinearGroup (Fin N) K :=
  { toFun := fun M => Matrix.SpecialLinearGroup.transpose M⁻¹
    invFun := fun M => Matrix.SpecialLinearGroup.transpose M⁻¹
    left_inv := by
      intro M
      change Matrix.SpecialLinearGroup.transpose
        (Matrix.SpecialLinearGroup.transpose M⁻¹)⁻¹ = M
      rw [transpose_inv', transpose_transpose', inv_inv]
    right_inv := by
      intro M
      change Matrix.SpecialLinearGroup.transpose
        (Matrix.SpecialLinearGroup.transpose M⁻¹)⁻¹ = M
      rw [transpose_inv', transpose_transpose', inv_inv]
    map_mul' := by
      intro M M'
      change Matrix.SpecialLinearGroup.transpose (M * M')⁻¹ =
        Matrix.SpecialLinearGroup.transpose M⁻¹ *
          Matrix.SpecialLinearGroup.transpose M'⁻¹
      rw [_root_.mul_inv_rev, transpose_mul'] }

theorem inverseTransposeSL_apply (N : ℕ) (K : Type) [Field K]
    (A : Matrix.SpecialLinearGroup (Fin N) K) :
    inverseTransposeSL N K A = Matrix.SpecialLinearGroup.transpose A⁻¹ := rfl

private lemma transpose_transvection {N : ℕ} {i j : Fin N} (hij : i ≠ j) (c : F) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.transvection, Matrix.single, Matrix.add_apply,
    Matrix.one_apply]
  by_cases h1 : j = a ∧ i = b
  · have h2 : i = b ∧ j = a := ⟨h1.2, h1.1⟩
    simp [h1, h2, eq_comm]
  · have h2 : ¬ (i = b ∧ j = a) := fun h => h1 ⟨h.2, h.1⟩
    simp [h1, h2, eq_comm]

theorem inverseTransposeSL_tv {N : ℕ} {i j : Fin N} (hij : i ≠ j) (c : F) :
    inverseTransposeSL N F (CFSG.Timmesfeld.tv i j c) = CFSG.Timmesfeld.tv j i (-c) := by
  rw [CFSG.Timmesfeld.tv_of_ne hij c, CFSG.Timmesfeld.tv_of_ne hij.symm (-c)]
  apply Subtype.ext
  change (((Matrix.SpecialLinearGroup.transpose
      (Matrix.SpecialLinearGroup.transvection hij c)⁻¹ :
        Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F)) =
    (Matrix.SpecialLinearGroup.transvection hij.symm (-c) : Matrix (Fin N) (Fin N) F)
  rw [Matrix.SpecialLinearGroup.transvection_inv]
  change ((Matrix.transvection i j (-c) : Matrix (Fin N) (Fin N) F))ᵀ =
    (Matrix.transvection j i (-c) : Matrix (Fin N) (Fin N) F)
  exact transpose_transvection hij (-c)

theorem inverseTransposeSL_blk (i : Fin 2) (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    inverseTransposeSL 3 F (blk F i B) =
      blk F i (inverseTransposeSL 2 F B) := by
  fin_cases i
  · have h : (inverseTransposeSL 3 F).toMonoidHom.comp (blk F 0) =
        (blk F 0).comp (inverseTransposeSL 2 F).toMonoidHom := by
      refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
      · change inverseTransposeSL 3 F (blk F 0 (CFSG.Timmesfeld.tv 0 1 c)) =
          blk F 0 (inverseTransposeSL 2 F (CFSG.Timmesfeld.tv 0 1 c))
        rw [blk_zero_tv01,
          inverseTransposeSL_tv (N := 3) (i := 0) (j := 1) (by decide) c,
          inverseTransposeSL_tv (N := 2) (i := 0) (j := 1) (by decide) c,
          blk_zero_tv10]
      · change inverseTransposeSL 3 F (blk F 0 (CFSG.Timmesfeld.tv 1 0 c)) =
          blk F 0 (inverseTransposeSL 2 F (CFSG.Timmesfeld.tv 1 0 c))
        rw [blk_zero_tv10,
          inverseTransposeSL_tv (N := 3) (i := 1) (j := 0) (by decide) c,
          inverseTransposeSL_tv (N := 2) (i := 1) (j := 0) (by decide) c,
          blk_zero_tv01]
    exact DFunLike.congr_fun h B
  · have h : (inverseTransposeSL 3 F).toMonoidHom.comp (blk F 1) =
        (blk F 1).comp (inverseTransposeSL 2 F).toMonoidHom := by
      refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
      · change inverseTransposeSL 3 F (blk F 1 (CFSG.Timmesfeld.tv 0 1 c)) =
          blk F 1 (inverseTransposeSL 2 F (CFSG.Timmesfeld.tv 0 1 c))
        rw [blk_one_tv01,
          inverseTransposeSL_tv (N := 3) (i := 1) (j := 2) (by decide) c,
          inverseTransposeSL_tv (N := 2) (i := 0) (j := 1) (by decide) c,
          blk_one_tv10]
      · change inverseTransposeSL 3 F (blk F 1 (CFSG.Timmesfeld.tv 1 0 c)) =
          blk F 1 (inverseTransposeSL 2 F (CFSG.Timmesfeld.tv 1 0 c))
        rw [blk_one_tv10,
          inverseTransposeSL_tv (N := 3) (i := 2) (j := 1) (by decide) c,
          inverseTransposeSL_tv (N := 2) (i := 1) (j := 0) (by decide) c,
          blk_one_tv01]
    exact DFunLike.congr_fun h B

end ActualInverseTransposeActor

section InverseTransposeRootBridge
open CFSG.RankThree.Classical

theorem inverseTransposeSL_two_eq_conjSL_swapGL {F : Type} [Field F] [CharP F 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    inverseTransposeSL 2 F A = CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.swapGL (K := F)) A := by
  apply Subtype.ext
  change (↑(Matrix.SpecialLinearGroup.transpose A⁻¹) : Matrix (Fin 2) (Fin 2) F) =
    ↑(CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.swapGL (K := F)) A)
  rw [Matrix.SpecialLinearGroup.coe_transpose]
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.swapGL_inv, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.adjugate_fin_two,
      CFSG.RankThree.Classical.swapGL, Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two,
      CharTwo.neg_eq]

theorem rootSL2_inverseTransposeSL {τ : Tag} {F : Type} [Field F] [CharP F 2]
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    rootSL2 τ F β (inverseTransposeSL 2 F A) =
      rootSL2 τ F (-β) A := by
  rw [inverseTransposeSL_two_eq_conjSL_swapGL]
  exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_neg_two (L := F) hβ A).symm

end InverseTransposeRootBridge

end CFSG.StandardType.GGFinModel

end
