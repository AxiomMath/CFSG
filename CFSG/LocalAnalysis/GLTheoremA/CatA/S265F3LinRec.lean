module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LieType.SemisimpleCentralizers.HeldLangSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {K : Type} [Field K]

theorem congr_recipeEquiv_twist {d : ℕ} (A : GL (Fin d) K) (σ : K ≃+* K)
    {u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hu : ∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x)) :
    MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv d K) u = conjAut d K A * fieldAut d K σ := by
  ext y
  obtain ⟨g, rfl⟩ := proj_surjective d K y
  obtain ⟨h, rfl⟩ : ∃ h : ↥(slGL (Fin d) K), CFSG.StandardType.TypeA.slKerEquiv d K h = g :=
    ⟨(CFSG.StandardType.TypeA.slKerEquiv d K).symm g, MulEquiv.apply_symm_apply _ g⟩
  have hg : proj d K (CFSG.StandardType.TypeA.slKerEquiv d K h) =
      CFSG.StandardType.TypeA.recipeEquiv d K (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h) :=
    rfl
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, MulAut.congr_apply, hg, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, MulEquiv.trans_apply, hu h]
  show proj d K (CFSG.StandardType.TypeA.slKerEquiv d K (slTwist σ A h)) = _
  apply congrArg (proj d K)
  ext i j
  rw [CFSG.StandardType.TypeA.coe_slConjugation']
  show ((slTwist σ A h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = _
  rw [coe_slTwist, Units.val_mul, Units.val_mul]
  rfl

theorem conjAut_mul_fieldAut_not_mem [Finite K] {d : ℕ} (hd : 3 ≤ d) (A : GL (Fin d) K)
    {σ : K ≃+* K} (hσ : σ ≠ 1) : conjAut d K A * fieldAut d K σ ∉ linearAutGroup d K := by
  intro hmem
  obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.1 hmem
  have h1 : conjAut d K (B⁻¹ * A) * fieldAut d K σ = 1 := by
    rw [map_mul, map_inv, mul_assoc, ← hB, inv_mul_cancel]
  exact hσ (CFSG.StandardType.RecipeFieldLinear.eq_one_of_conjAut_mul_fieldAut_eq_one'
    (by omega) (Or.inl hd) _ σ h1).1

theorem congr_not_mem_linearAutGroup [Finite K] {S : Type} [Group S] {d : ℕ} (hd : 3 ≤ d)
    {α : MulAut S} (A : GL (Fin d) K) {σ : K ≃+* K} (hσ : σ ≠ 1)
    {u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (e : S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) (heu : ∀ l, e (α l) = u (e l))
    (hu : ∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x)) :
    MulAut.congr (e.trans (CFSG.StandardType.TypeA.recipeEquiv d K)) α ∉ linearAutGroup d K := by
  have h1 : MulAut.congr e α = u := by
    ext y
    obtain ⟨l, rfl⟩ := e.surjective y
    show e (α (e.symm (e l))) = u (e l)
    rw [MulEquiv.symm_apply_apply, heu]
  have h2 : MulAut.congr (e.trans (CFSG.StandardType.TypeA.recipeEquiv d K)) α =
      MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv d K) (MulAut.congr e α) := by
    ext y
    rfl
  rw [h2, h1, congr_recipeEquiv_twist A σ hu]
  exact conjAut_mul_fieldAut_not_mem hd A hσ

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
