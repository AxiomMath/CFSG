module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSetup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding.LinearThreeKit

section Core

variable {Y : Type} [Group Y] {L : Subgroup Y} {K : Type} [Field K]

theorem exists_setup' [Finite Y] [Finite K] [CharP K 2] {J : Subgroup Y} (hCP : CompParab L J)
    (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) :
    ∃ (g' : Matrix.SpecialLinearGroup (Fin 3) K) (d : ℕ), (d = 1 ∨ d = 2) ∧
      ∀ l : ↥L, (l : Y) ∈ J ↔ MulAut.conj g'⁻¹ (ψ l) ∈ stabilizer (flagSpace 3 K d) := by
  obtain ⟨g, d, hd, hJ⟩ := exists_eq_map_conj_projStabilizer (projEquiv ψ) hCP
  obtain ⟨g', rfl⟩ := proj_surjective 3 K g
  refine ⟨g', d, hd, fun l => ?_⟩
  rw [← censusHom_mem_map_iff (projEquiv ψ) hCP.parab, hJ, censusHom_projEquiv,
    Subgroup.mem_map_equiv]
  rw [← comap_projStabilizer, Subgroup.mem_comap]
  have : (MulAut.conj (proj 3 K g')).symm (proj 3 K (ψ l)) =
      proj 3 K (MulAut.conj g'⁻¹ (ψ l)) := by
    simp [MulAut.conj_symm_apply, proj]
  rw [this]

end Core

theorem toGL_conj_of_conj {K : Type} [Field K] {B : Type} [Group B]
    (ψ₀ : B ≃* Matrix.SpecialLinearGroup (Fin 3) K) (g' : Matrix.SpecialLinearGroup (Fin 3) K)
    (φ : B → B) (A' : GL (Fin 3) K)
    (h : ∀ l : B, MulAut.conj g'⁻¹ (ψ₀ (φ l)) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A'
        (MulAut.conj g'⁻¹ (ψ₀ l))) (l : B) :
    Matrix.SpecialLinearGroup.toGL (ψ₀ (φ l)) =
      (Matrix.SpecialLinearGroup.toGL g' * A' * (Matrix.SpecialLinearGroup.toGL g')⁻¹) *
        Matrix.SpecialLinearGroup.toGL (ψ₀ l) *
        (Matrix.SpecialLinearGroup.toGL g' * A' * (Matrix.SpecialLinearGroup.toGL g')⁻¹)⁻¹ := by
  have h1 := congrArg Matrix.SpecialLinearGroup.toGL (h l)
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation] at h1
  have e1 : ∀ x : Matrix.SpecialLinearGroup (Fin 3) K, MulAut.conj g'⁻¹ x = g'⁻¹ * x * g' := by
    intro x
    simp
  rw [e1, e1] at h1
  simp only [map_mul, map_inv] at h1
  set N := Matrix.SpecialLinearGroup.toGL (ψ₀ (φ l))
  set M := Matrix.SpecialLinearGroup.toGL (ψ₀ l)
  set ĝ := Matrix.SpecialLinearGroup.toGL g'
  calc N = ĝ * (ĝ⁻¹ * N * ĝ) * ĝ⁻¹ := by group
    _ = ĝ * (A' * (ĝ⁻¹ * M * ĝ) * A'⁻¹) * ĝ⁻¹ := by rw [h1]
    _ = _ := by group

end CFSG.HardMathSupport.Curtis.Coordinator
