module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.SignalizerFunctorTheorem.NonLocal.LinearMain
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.GLTheoremA.FQ
  CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.LocalAnalysis.GLTheoremA.MI CFSG.RankThree.PartOne

section Equiv

variable (d : ℕ) (K : Type) [Field K]

theorem statedSL_eq_largeEvenSL : StatedSL d K = LargeEvenSLGroup (Fin d) K := by
  ext A
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, mem_LargeEvenSL_iff]

@[expose] noncomputable def slEquivLargeEven :
    Matrix.SpecialLinearGroup (Fin d) K ≃* LargeEvenSLGroup (Fin d) K :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d K).trans
    (MulEquiv.subgroupCongr (statedSL_eq_largeEvenSL d K))

theorem slEquivLargeEven_coe (A : Matrix.SpecialLinearGroup (Fin d) K) :
    ((slEquivLargeEven d K A : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) =
      Matrix.SpecialLinearGroup.toGL A :=
  Units.ext rfl

theorem map_scalars_slEquivLargeEven :
    (scalars d K).map (slEquivLargeEven d K).toMonoidHom =
      (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K) := by
  have h := CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars d K
  rw [← scalars_eq_center] at h
  ext x
  obtain ⟨A, rfl⟩ := (slEquivLargeEven d K).surjective x
  have h1 : (slEquivLargeEven d K A) ∈ (scalars d K).map (slEquivLargeEven d K).toMonoidHom ↔
      A ∈ scalars d K := by
    constructor
    · rintro ⟨B, hB, hBA⟩
      rwa [← (slEquivLargeEven d K).injective hBA]
    · intro hA
      exact ⟨A, hA, rfl⟩
  have h2 : A ∈ scalars d K ↔
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d K A) ∈
        (CFSG.Open.StatedScalars (Fin d) K).subgroupOf (StatedSL d K) := by
    rw [← h]
    constructor
    · intro hA
      exact ⟨A, hA, rfl⟩
    · rintro ⟨B, hB, hBA⟩
      rwa [← (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d K).injective hBA]
  rw [h1, h2, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  rfl

@[expose] noncomputable def linRecipeEquiv :
    projectiveSL d K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K) :=
  QuotientGroup.congr (scalars d K) _ (slEquivLargeEven d K) (map_scalars_slEquivLargeEven d K)

theorem linRecipeEquiv_proj (A : Matrix.SpecialLinearGroup (Fin d) K) :
    linRecipeEquiv d K (proj d K A) = QuotientGroup.mk (slEquivLargeEven d K A) :=
  QuotientGroup.congr_mk _ _ _ _ A

end Equiv

section Witness

variable {d : ℕ} {K : Type} [Field K] [Finite K]

theorem fixed_of_subfield {σ : K ≃+* K}
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hσ : ∀ x : LargeEvenSLGroup (Fin d) K, f (QuotientGroup.mk x) =
      QuotientGroup.mk (matAct (LargeEvenSLGroup (Fin d) K) (fun σ h hh => sl_map_mem σ h hh) σ x))
    (k : Subfield K) (hk : ∀ c ∈ k, σ c = c) :
    ((linearSubfieldInclusion d k).range).map (linRecipeEquiv d K).toMonoidHom ≤ fixSub f := by
  rintro _ ⟨y, ⟨z, rfl⟩, rfl⟩
  obtain ⟨A, rfl⟩ := proj_surjective d k z
  rw [linearSubfieldInclusion_proj]
  show f (linRecipeEquiv d K (proj d K (Matrix.SpecialLinearGroup.map k.subtype A))) =
    linRecipeEquiv d K (proj d K (Matrix.SpecialLinearGroup.map k.subtype A))
  rw [linRecipeEquiv_proj, hσ]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp only [matAct_coe, coe_glMap, slEquivLargeEven_coe, Matrix.map_apply]
  exact hk _ (A i j).2

theorem nlWitness_linear (hd : 3 ≤ d)
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) :
    NLWitness f := by
  obtain ⟨σ, hσ⟩ := matField_spec (LargeEvenSLGroup (Fin d) K) (fun σ h hh => sl_map_mem σ h hh) hf
  obtain ⟨hs, hna⟩ := simple_nonabelian_range_linearSubfieldInclusion hd (fixF σ)
  refine nlWitness_of_nonLocalized (linRecipeEquiv d K).symm hs ?_
    (CFSG.SignalizerFunctorTheorem.NonLocal.nonLocalized_linearSubfield hd (fixF σ)) ?_
  · by_contra hcon
    push Not at hcon
    exact hna fun x y => hcon x y
  · rw [MulEquiv.symm_symm]
    exact fixed_of_subfield hσ (fixF σ) (fun c hc => hc)

end Witness

section Two

@[expose] noncomputable def psl2RecipeEquiv (K : Type) [Field K] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) K) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).trans (linRecipeEquiv 2 K)

theorem noLocalTwo_linear_two {p : ℕ} (hp : p.Prime) {K : Type}
    [Field K] [Finite K] (β : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))) :
    NoLocalTwo p β :=
  noLocalTwo_of_psl2 hp (psl2RecipeEquiv K).symm β

end Two

section Family

set_option linter.unusedSectionVars false


theorem i2015NLOnLinear_holds : I2015NLOnLinear := by
  intro lab hlab ht
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  by_cases hr : r = 1
  · subst hr
    intro p hp hp2 h3 _ Q hQ
    dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', fun _ _ f _ _ _ => noLocalTwo_linear_two hp f⟩
  · have hr2 : 2 ≤ r := by
      have := hlab.2
      dsimp only at this
      omega
    refine atLabelWhen_of_witness hlab ?_ (fun p _ => by simp)
    intro p hp hp2 h3 hexc _ Q hQ
    dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf _ _ _ => nlWitness_linear (by omega) hf⟩

theorem i2015NLOnD3_holds : I2015NLOnD3 := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_ (fun p _ h => by rw [ht] at h; exact absurd h.1 (by decide))
  intro p hp hp2 h3 hexc hC
  obtain ⟨t, r, n⟩ := lab
  dsimp only [regRank] at hC ht
  subst hC
  subst ht
  intro Q hQ
  simp only [CFSG.Assembly.LargeEvenRawDatum, if_true] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf _ _ _ => nlWitness_linear (by norm_num) hf⟩

theorem i2015NLOnTwD2_holds : I2015NLOnTwD2 := by
  intro lab hlab ht p hp hp2 h3 hC
  obtain ⟨t, r, n⟩ := lab
  dsimp only [regRank] at hC ht
  subst hC
  subst ht
  intro Q hQ
  simp only [CFSG.Assembly.LargeEvenRawDatum, if_true] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ', fun _ _ f _ _ _ => noLocalTwo_linear_two hp f⟩

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
