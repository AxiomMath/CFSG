module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearAction

public section

namespace CFSG.LieType.ChevTwo.OppCl

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBLinearSemilinear

section Odd

variable (n : ℕ) (F : Type) [Field F]

def semilinSub : Subgroup (MulAut (projectiveSL n F)) where
  carrier := {α | ∃ (A : GL (Fin n) F) (σ : F ≃+* F), α = conjAut n F A * fieldAut n F σ}
  one_mem' := ⟨1, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨A, σ, rfl⟩ ⟨B, τ, rfl⟩
    obtain ⟨-, -, hfc, -⟩ := (standard_automorphism_transport (n := n) (K := F))
    refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) B, σ * τ, ?_⟩
    have h3 : fieldAut n F σ * conjAut n F B =
        conjAut n F (GeneralLinearGroup.map (σ : F →+* F) B) * fieldAut n F σ := by
      have := hfc σ B
      rwa [mul_inv_eq_iff_eq_mul] at this
    calc conjAut n F A * fieldAut n F σ * (conjAut n F B * fieldAut n F τ)
        = conjAut n F A * (fieldAut n F σ * conjAut n F B) * fieldAut n F τ := by
          simp only [mul_assoc]
      _ = conjAut n F A * (conjAut n F (GeneralLinearGroup.map (σ : F →+* F) B) *
            fieldAut n F σ) * fieldAut n F τ := by rw [h3]
      _ = (conjAut n F A * conjAut n F (GeneralLinearGroup.map (σ : F →+* F) B)) *
            (fieldAut n F σ * fieldAut n F τ) := by simp only [mul_assoc]
      _ = conjAut n F (A * GeneralLinearGroup.map (σ : F →+* F) B) * fieldAut n F (σ * τ) := by
          rw [map_mul, map_mul]
  inv_mem' := by
    rintro _ ⟨A, σ, rfl⟩
    obtain ⟨-, -, hfc, -⟩ := (standard_automorphism_transport (n := n) (K := F))
    refine ⟨GeneralLinearGroup.map ((σ⁻¹ : F ≃+* F) : F →+* F) A⁻¹, σ⁻¹, ?_⟩
    have h3 : fieldAut n F σ⁻¹ * conjAut n F A⁻¹ =
        conjAut n F (GeneralLinearGroup.map ((σ⁻¹ : F ≃+* F) : F →+* F) A⁻¹) *
          fieldAut n F σ⁻¹ := by
      have := hfc σ⁻¹ A⁻¹
      rwa [mul_inv_eq_iff_eq_mul] at this
    rw [_root_.mul_inv_rev, ← map_inv, ← map_inv, h3]

theorem mem_semilinSub_of_odd_pow [Finite F] (hn : 3 ≤ n) {α : MulAut (projectiveSL n F)}
    {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) : α ∈ semilinSub n F := by
  obtain ⟨-, hform⟩ := LinearFlag.automorphism_generation (K := F) hn
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  obtain ⟨-, -, -, hδδ, hδc, hδf, -⟩ := (standard_automorphism_transport (n := n) (K := F))
  have he : conjAut n F A * fieldAut n F σ ∈ semilinSub n F := ⟨A, σ, rfl⟩
  have hsq : α ^ 2 ∈ semilinSub n F := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · rw [pow_zero, mul_one] at hαeq
      rw [hαeq, pow_two]
      exact mul_mem he he
    · rw [pow_one] at hαeq
      have hconj : dualAut n F * (conjAut n F A * fieldAut n F σ) * dualAut n F =
          conjAut n F (GeneralLinearGroup.inverseTranspose A) * fieldAut n F σ := by
        calc dualAut n F * (conjAut n F A * fieldAut n F σ) * dualAut n F
            = dualAut n F * conjAut n F A * (dualAut n F * dualAut n F) * fieldAut n F σ *
                dualAut n F := by rw [hδδ]; simp only [mul_assoc, mul_one]
          _ = (dualAut n F * conjAut n F A * dualAut n F) *
                (dualAut n F * fieldAut n F σ * dualAut n F) := by simp only [mul_assoc]
          _ = _ := by rw [hδc A, hδf σ]
      have : α ^ 2 = (conjAut n F A * fieldAut n F σ) *
          (dualAut n F * (conjAut n F A * fieldAut n F σ) * dualAut n F) := by
        rw [hαeq, pow_two]
        simp only [mul_assoc]
      rw [this, hconj]
      exact mul_mem he ⟨_, σ, rfl⟩
  obtain ⟨j, hj⟩ := hm
  have : α = (α ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = m + 1 by omega, pow_succ, hα, one_mul]
  rw [this]
  exact pow_mem hsq _

end Odd

section Transport

variable (n : ℕ) (F : Type) [Field F]

theorem projEquiv_semilinearAction (A : GL (Fin n) F) (σ : F ≃+* F)
    (x : ProjectiveSpecialLinearGroup (Fin n) F) :
    LinearCover.projectiveSpecialLinearEquivProjectiveSL n F (semilinearAction n F A σ x) =
      (conjAut n F A * fieldAut n F σ)
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (SpecialLinearGroup (Fin n) F)) x
  rw [semilinearAction_mk]
  rfl

theorem congr_semilinearAction (A : GL (Fin n) F) (σ : F ≃+* F) :
    MulAut.congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F)
        (semilinearAction n F A σ) = conjAut n F A * fieldAut n F σ := by
  ext x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    projEquiv_semilinearAction, MulEquiv.apply_symm_apply]

theorem exists_conj_of_odd_pow [Finite F] (hn : 3 ≤ n) {m : ℕ} (hm : Odd m)
    (α : MulAut (StatedProj (StatedSL n F))) (hα : α ^ m = 1) :
    ∃ (A : GL (Fin n) F) (σ : F ≃+* F), ∀ h : StatedSL n F, ∃ h' : StatedSL n F,
      ((h' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (A : Matrix (Fin n) (Fin n) F) * ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∧
      α (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) h) =
        QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) h' := by
  set E₁ := LinearCover.projectiveSpecialLinearEquivProjectiveSL n F with hE₁
  set E₂ := projectiveSpecialLinearGroupEquivStatedProj n F with hE₂
  set α₁ : MulAut (ProjectiveSpecialLinearGroup (Fin n) F) := MulAut.congr E₂.symm α with hα₁
  set α' : MulAut (projectiveSL n F) := MulAut.congr E₁ α₁ with hα'
  have hα'm : α' ^ m = 1 := by
    rw [hα', hα₁, ← map_pow, ← map_pow, hα, map_one, map_one]
  obtain ⟨A, σ, hA⟩ := mem_semilinSub_of_odd_pow n F hn hm hα'm
  have h1 : α₁ = semilinearAction n F A σ := by
    apply (MulAut.congr E₁).injective
    rw [congr_semilinearAction, ← hA]
  refine ⟨A, σ, fun h => ?_⟩
  obtain ⟨ĝ, rfl⟩ := (specialLinearGroupEquivStatedSL n F).surjective h
  refine ⟨specialLinearGroupEquivStatedSL n F (slSemilinearAction n F A σ ĝ), ?_, ?_⟩
  · rw [specialLinearGroupEquivStatedSL_coe, slSemilinearAction_matrix,
      specialLinearGroupEquivStatedSL_coe]
    rfl
  · have h2 : α (E₂ (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) ĝ)) =
        E₂ (α₁ (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) ĝ)) := by
      rw [hα₁]
      simp
    rw [h1, semilinearAction_mk] at h2
    exact h2

end Transport

end CFSG.LieType.ChevTwo.OppCl
