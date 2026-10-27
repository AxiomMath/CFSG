module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCoefficientSquare
public noncomputable section

namespace CFSG.StandardType.GGFinModel


open CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open scoped MatrixGroups commutatorElement


open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG.GroupTheory


open CFSG.EvenSmallLie.TwoE6 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.StandardType.TableBExc.E6Three
set_option allowUnsafeReducibility true in
attribute [local reducible] TwistTag.tag langTag

set_option backward.isDefEq.respectTransparency false in
theorem qTwo_corrected_source_action_eq_toral_lift
    (β α : MulAut (twistedE6Group 2 1)) (δ : MulAut stdGroup)
    (mu : stdGroup →* ModGL Tag.E6 GGL) (g0 : ModGL Tag.E6 GGL)
    (hsource : ∀ u, mu (isogenyStd (β u)) =
      (MulAut.conj g0).symm (ggIotaK .twistedE6 0 1 (by decide) u))
    (hα : ∀ u, isogenyStd (α u) = δ (isogenyStd u))
    (a : Fin Tag.E6.rank → GGLˣ)
    (hact : ∀ s, mu (δ s) = rootDiagUnit Tag.E6 a * mu s *
      (rootDiagUnit Tag.E6 a)⁻¹)
    (c d : e6Data_valid.minGroup GGL)
    (hc : e6IsogenyAlgebraic c = g0)
    (hd : e6IsogenyAlgebraic d = rootDiagUnit Tag.E6 a) :
    ∀ u, twFinEmbedding 0 1 (β.symm (α (β u))) =
      (MulAut.conj (c * d * c⁻¹)) (twFinEmbedding 0 1 u) := by
  let f1 : twistedE6Group 2 1 →* e6Data_valid.minGroup GGL :=
    (twFinEmbedding 0 1).comp
      (β.symm.toMonoidHom.comp (α.toMonoidHom.comp β.toMonoidHom))
  let f2 : twistedE6Group 2 1 →* e6Data_valid.minGroup GGL :=
    (MulAut.conj (c * d * c⁻¹)).toMonoidHom.comp (twFinEmbedding 0 1)
  have hi (u : twistedE6Group 2 1) :
      e6IsogenyAlgebraic (twFinEmbedding 0 1 u) = ggIotaK .twistedE6 0 1 (by decide) u :=
    (ggIotaK_twistedE6_eq_isogeny_minBC 0 1 (by decide) u).symm
  have heq (u : twistedE6Group 2 1) : e6IsogenyAlgebraic (f1 u) =
      e6IsogenyAlgebraic (f2 u) := by
    have hh := hact (isogenyStd (β u))
    rw [← hα] at hh
    have hβ : β (β.symm (α (β u))) = α (β u) := β.apply_symm_apply _
    rw [← hβ, hsource, hsource] at hh
    have hconj := congrArg (MulAut.conj g0) hh
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at hconj
    change e6IsogenyAlgebraic (twFinEmbedding 0 1 (β.symm (α (β u)))) =
      e6IsogenyAlgebraic
        ((c * d * c⁻¹) * twFinEmbedding 0 1 u * (c * d * c⁻¹)⁻¹)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hc, hd, hi, hi]
    exact hconj
  have hf := CFSG.RankThree.PartOne.hom_eq_of_div_central
    isPerfect_twistedE6Group f1 f2 fun u => by
      rw [← ker_e6IsogenyAlgebraic_eq_center]
      change e6IsogenyAlgebraic (f1 u * (f2 u)⁻¹) = 1
      rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact fun u => DFunLike.congr_fun hf u

set_option backward.isDefEq.respectTransparency false in
theorem qTwo_corrected_whole_donor_fixed_of_two_root_chars
    (β α : MulAut (twistedE6Group 2 1)) (δ : MulAut stdGroup)
    (mu : stdGroup →* ModGL Tag.E6 GGL) (g0 : ModGL Tag.E6 GGL)
    (hsource : ∀ u, mu (isogenyStd (β u)) =
      (MulAut.conj g0).symm (ggIotaK .twistedE6 0 1 (by decide) u))
    (hα : ∀ u, isogenyStd (α u) = δ (isogenyStd u))
    (a : Fin Tag.E6.rank → GGLˣ)
    (hact : ∀ s, mu (δ s) = rootDiagUnit Tag.E6 a * mu s *
      (rootDiagUnit Tag.E6 a)⁻¹)
    (Ψ : SL(3, actualQuadraticSubfield 1) →*
      e6Data_valid.minGroup (actualQuadraticSubfield 1))
    (ρ : SL(3, actualQuadraticSubfield 1) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield 1))
    (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield 1)).comp Ψ)
    (hframe : CFSG.RankThree.PartOne.KF4.IsA2Frame
      ((adjointGroup Tag.E6 (actualQuadraticSubfield 1)).subtype.comp ρ) σ)
    (c d : e6Data_valid.minGroup GGL)
    (hc : e6IsogenyAlgebraic c = g0)
    (hd : e6IsogenyAlgebraic d = rootDiagUnit Tag.E6 a)
    (theta : Su (actualQuadraticSubfield 1) 2 1 3 →* twistedE6Group 2 1)
    (hmin : (twFinEmbedding 0 1).comp theta =
      (MulAut.conj c).toMonoidHom.comp
        (((minBC e6Data_valid (actualQuadraticSubfield 1).subtype).comp Ψ).comp
          (CFSG.ClassicalInvolution.Models.suToSL
            (unitaryInvolution (actualQuadraticSubfield 1) 2 1) 3)))
    (hchar0 : rootChar a (σ 0 1) = 1)
    (hchar1 : rootChar a (σ 1 2) = 1) :
    ∀ A, α (β (theta A)) = β (theta A) := by
  intro A
  have hmat := qTwo_corrected_source_action_eq_toral_lift β α δ mu g0
    hsource hα a hact c d hc hd (theta A)
  have hminA := DFunLike.congr_fun hmin A
  change twFinEmbedding 0 1 (theta A) =
    c * ((minBC e6Data_valid (actualQuadraticSubfield 1).subtype).comp Ψ)
      (CFSG.ClassicalInvolution.Models.suToSL
        (unitaryInvolution (actualQuadraticSubfield 1) 2 1) 3 A) * c⁻¹ at hminA
  have hcomm := e6_common_lang_compact_image_centralizes_toral_lift
    Ψ ρ σ hρ hframe a hchar0 hchar1 d c hd A
  have hfixed : twFinEmbedding 0 1 (β.symm (α (β (theta A)))) =
      twFinEmbedding 0 1 (theta A) := by
    rw [hmat, hminA]
    change (c * d * c⁻¹) *
      (c * ((minBC e6Data_valid (actualQuadraticSubfield 1).subtype).comp Ψ)
        (CFSG.ClassicalInvolution.Models.suToSL
          (unitaryInvolution (actualQuadraticSubfield 1) 2 1) 3 A) * c⁻¹) *
        (c * d * c⁻¹)⁻¹ = _
    rw [hcomm]
    group
  have heq := twFinEmbedding_injective 0 1 hfixed
  apply β.symm.injective
  simpa only [MulEquiv.symm_apply_apply] using heq

end CFSG.StandardType.GGFinModel
