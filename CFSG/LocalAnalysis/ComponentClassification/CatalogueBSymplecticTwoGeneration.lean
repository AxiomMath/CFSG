module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoOrthogonality

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Matrix Module Submodule CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

variable {K : Type} [Field K]

theorem mulVecLin_injective_of_gl (A : GL (Fin 2 ⊕ Fin 2) K) :
    Function.Injective (mulVecLin (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
  intro u v h
  have := congrArg (fun z => ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ z) h
  simp only [mulVecLin_apply, mulVec_mulVec] at this
  rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, one_mulVec] at this

theorem conjAut_mem_typeKernel (A : gsp 2 K) : conjAut 2 K A ∈ typeKernel K := by
  have key : ∀ B : gsp 2 K, ∀ M ∈ pointParabolics K,
      M.map (conjAut 2 K B).toMonoidHom ∈ pointParabolics K := by
    rintro B _ ⟨L, hL, rfl⟩
    refine ⟨L.map (mulVecLin ((B : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)), ?_, map_projStabilizer_conjAut B L⟩
    rw [← (Submodule.equivMapOfInjective _ (mulVecLin_injective_of_gl (B : GL _ K)) L).finrank_eq,
      hL]
  refine mem_typeKernel_of_forall (key A) fun M hM => ?_
  rw [← map_inv]
  exact key A⁻¹ M hM

theorem fieldAut_mem_typeKernel (σ : K ≃+* K) : fieldAut 2 K σ ∈ typeKernel K := by
  have key : ∀ τ : K ≃+* K, ∀ M ∈ pointParabolics K,
      M.map (fieldAut 2 K τ).toMonoidHom ∈ pointParabolics K := by
    rintro τ _ ⟨L, hL, rfl⟩
    refine ⟨spCoordImage τ L, ?_, map_projStabilizer_fieldAut τ L⟩
    obtain ⟨v, hv, hLv⟩ := SpPoint.exists_ofVec (⟨L, hL⟩ : SpPoint 2 K)
    have hL' : L = span K {v} := congrArg SpPoint.line hLv
    rw [hL', spCoordImage_span_singleton, finrank_span_singleton (coord_ne_zero τ hv)]
  refine mem_typeKernel_of_forall (key σ) fun M hM => ?_
  rw [← map_inv]
  exact key σ⁻¹ M hM

theorem spSemilinearAutGroup_le_typeKernel : spSemilinearAutGroup 2 K ≤ typeKernel K := by
  have hD : spLinearAutGroup 2 K ≤ typeKernel K := by
    rw [spLinearAutGroup, Subgroup.closure_le]
    rintro _ ⟨A, rfl⟩
    exact conjAut_mem_typeKernel A
  rw [spSemilinearAutGroup, Subgroup.closure_le]
  rintro α (hα | ⟨σ, rfl⟩)
  · exact hD hα
  · exact fieldAut_mem_typeKernel σ

theorem exists_eq_conjAut_mul_fieldAut [Finite K] {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : α ∈ typeKernel K) :
    ∃ (A : gsp 2 K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ := by
  obtain ⟨⟨f, hf, -⟩, ⟨h, hh, -⟩, hrel⟩ := kernel_orthogonality hα
  obtain ⟨-, horth⟩ := hrel f h hf hh
  obtain ⟨A, σ, μ, hA, hfL⟩ := geometric_semilinear_realization (by norm_num : 2 ≤ 2) f horth
  refine ⟨⟨A, μ, hA⟩, σ, LinearFlag.equivariant_subgroup_rigidity
    (fun L : SpPoint 2 K => projStabilizer 2 K L.line) pointStabilizer_injective
    projStabilizer_smul α _ f f.bijective hf fun L => ?_⟩
  rw [map_projStabilizer_conjAut_mul_fieldAut, ← hfL L]

theorem kernel_generation [Finite K] :
    typeKernel K = spSemilinearAutGroup 2 K ∧
    (∀ α ∈ typeKernel K, ∃ (A : gsp 2 K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ) ∧
    (spSemilinearAutGroup 2 K).Normal ∧ (spSemilinearAutGroup 2 K).index ≤ 2 := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, hnormal, hindex, -⟩ := type_kernel (K := K) p
  have hHE : typeKernel K = spSemilinearAutGroup 2 K := by
    refine le_antisymm (fun α hα => ?_) spSemilinearAutGroup_le_typeKernel
    obtain ⟨A, σ, rfl⟩ := exists_eq_conjAut_mul_fieldAut hα
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  exact ⟨hHE, fun α hα => exists_eq_conjAut_mul_fieldAut hα, hHE ▸ hnormal, hHE ▸ hindex⟩

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
