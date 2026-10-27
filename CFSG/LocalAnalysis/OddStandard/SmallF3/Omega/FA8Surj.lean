module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8Std
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8Equiv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJAut8Img
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer

private theorem fa8_ringEquiv_zmod_three (σ : ZMod 3 ≃+* ZMod 3) : σ = 1 := by
  apply RingEquiv.ext
  intro x
  exact congrArg (fun f : ZMod 3 →+* ZMod 3 => f x) (RingHom.ext_zmod σ.toRingHom (RingHom.id _))

theorem fa8_ffSimOmegaAct_surjective_std (hQ : fa8Q0.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Fin (2 * 4) → ZMod 3)) :
    Function.Surjective (ffSimOmegaAct hQ h2 : ProjSim fa8Q0 →* MulAut (omegaProj hQ)) := by
  intro α
  have hne : ∃ v, fa8Q0 v ≠ 0 := by
    obtain ⟨v, hv⟩ := hQ.exists_isUnit
    exact ⟨v, hv.ne_zero⟩
  have himg : matrixProjectiveImage fa8Q0 = ⊤ := fj_matrixProjectiveImage_eight_minus (by norm_num)
  let Ψ : matrixProjectiveDerived fa8Q0 ≃* omegaProj hQ :=
    (projectiveEquiv fa8Q0 hne).trans (fa8ProjDerivedEquiv hQ h2)
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff fa8Q0 ((MulAut.congr Ψ).symm α)).mp
    (by rw [himg]; exact Subgroup.mem_top _)
  have hright : g.val.right = 1 := fa8_ringEquiv_zmod_three _
  refine ⟨QuotientGroup.mk ⟨matrixLinearEquiv g.val.left, multiplier fa8Q0 g,
    matrix_similarity fa8Q0 g hright⟩, ?_⟩
  apply MulEquiv.ext
  intro w
  obtain ⟨x, rfl⟩ := Ψ.surjective w
  have hα : α (Ψ x) = Ψ ((MulAut.congr Ψ).symm α x) := by
    have h := congrArg (fun f : MulAut (omegaProj hQ) => f (Ψ x))
      ((MulAut.congr Ψ).apply_symm_apply α).symm
    simpa using h
  rw [hα, ← hg]
  change _ = fa8ProjDerivedEquiv hQ h2 (projectiveEquiv fa8Q0 hne
    (matrixProjectiveConjugation fa8Q0 g x))
  rw [projectiveEquiv_conjugation_linear fa8Q0 hne g hright x,
    fa8ProjDerivedEquiv_projectiveConjugation]
  rfl

end CFSG.OddStandard.SmallF3.Omega
