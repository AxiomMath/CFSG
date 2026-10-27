module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsLinAut
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {d : ℕ}

theorem congr_congr_symm_recipe (x : MulAut (projectiveSL d K)) :
    MulAut.congr (TypeA.recipeEquiv d K) (MulAut.congr (TypeA.recipeEquiv d K).symm x) = x := by
  ext y
  simp [MulAut.congr_apply]

theorem mem_fieldImage_of_congr (φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (σ : K ≃+* K) (h : MulAut.congr (TypeA.recipeEquiv d K) φ = fieldAut d K σ) :
    φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) := by
  refine ⟨σ, fun x y hxy => ?_⟩
  apply (TypeA.recipeEquiv d K).injective
  have h1 : ∀ z, TypeA.recipeEquiv d K (φ z) = fieldAut d K σ (TypeA.recipeEquiv d K z) := by
    intro z
    have := congrArg (fun F => F (TypeA.recipeEquiv d K z)) h
    simpa [MulAut.congr_apply] using this
  rw [h1, TypeA.recipeEquiv_mk, TypeA.recipeEquiv_mk, fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, TypeA.coe_slKerEquiv]
  have hij := congrFun (congrFun hxy i) j
  simp only [Matrix.map_apply] at hij
  simp [hij]

theorem recipe_dichotomy [Finite K] [CharP K 2] {p : ℕ} (hd : 2 ≤ d) (hp : Odd p)
    (φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) (hφ : φ ^ p = 1) :
    φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ ∨
      ∃ i ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
        ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)), φ = i * f := by
  have hφ' : (MulAut.congr (TypeA.recipeEquiv d K) φ) ^ p = 1 := by
    rw [← map_pow, hφ, map_one]
  obtain ⟨A, σ, h⟩ := odd_order_aut_eq_conj_mul_field' hd hp _ hφ'
  by_cases hI : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ
  · exact Or.inl hI
  · right
    refine ⟨MulAut.congr (TypeA.recipeEquiv d K).symm (conjAut d K A), ?_,
      MulAut.congr (TypeA.recipeEquiv d K).symm (fieldAut d K σ), ?_, ?_⟩
    · exact TypeA.mem_of_congr_recipeEquiv_mem ⟨A, (congr_congr_symm_recipe _).symm⟩
    · exact mem_fieldImage_of_congr _ σ (congr_congr_symm_recipe _)
    · have key : MulAut.congr (TypeA.recipeEquiv d K).symm
          (MulAut.congr (TypeA.recipeEquiv d K) φ) = φ := by
        ext y
        simp [MulAut.congr_apply]
      rw [← key, h, map_mul]

end CFSG.LocalAnalysis.GLTheoremA.Y10GField
