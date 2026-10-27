module

public import CFSG.ClassicalInvolution.Asc77.AscT7ML

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
abbrev PU : Type := Su K p f 4 ⧸ Subgroup.center (Su K p f 4)

@[expose] def ActsAsM (φ : MulAut (PU K p f)) (M Mi : Matrix (Fin 4) (Fin 4) K) : Prop :=
  M * Mi = 1 ∧ Mi * M = 1 ∧ ∀ h : Su K p f 4, ∃ h' : Su K p f 4,
    φ (QuotientGroup.mk h) = QuotientGroup.mk h' ∧ suMat h' = M * suMat h * Mi

theorem actsAsM_conj (g : Su K p f 4) :
    ActsAsM (MulAut.conj (QuotientGroup.mk g : PU K p f)) (suMat g) (suMat g⁻¹) := by
  refine ⟨suMat_mul_suMat_inv g, suMat_inv_mul_suMat g, fun h => ⟨g * h * g⁻¹, ?_, ?_⟩⟩
  · simp [MulAut.conj_apply]
  · rw [suMat_mul, suMat_mul]

theorem ActsAsM.mul {φ ψ : MulAut (PU K p f)} {M Mi N Ni : Matrix (Fin 4) (Fin 4) K}
    (hφ : ActsAsM φ M Mi) (hψ : ActsAsM ψ N Ni) : ActsAsM (φ * ψ) (M * N) (Ni * Mi) := by
  obtain ⟨hM1, hM2, hφ'⟩ := hφ
  obtain ⟨hN1, hN2, hψ'⟩ := hψ
  refine ⟨?_, ?_, fun h => ?_⟩
  · calc M * N * (Ni * Mi) = M * (N * Ni) * Mi := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hN1, Matrix.mul_one, hM1]
  · calc Ni * Mi * (M * N) = Ni * (Mi * M) * N := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM2, Matrix.mul_one, hN2]
  · obtain ⟨h₁, hh₁, hmat₁⟩ := hψ' h
    obtain ⟨h₂, hh₂, hmat₂⟩ := hφ' h₁
    refine ⟨h₂, ?_, ?_⟩
    · rw [MulAut.mul_apply, hh₁, hh₂]
    · rw [hmat₂, hmat₁]
      simp only [Matrix.mul_assoc]

theorem ActsAsM.comm {φ ψ : MulAut (PU K p f)} {M Mi N Ni : Matrix (Fin 4) (Fin 4) K}
    (hφ : ActsAsM φ M Mi) (hψ : ActsAsM ψ N Ni) (hMN : M * N = N * M) : φ * ψ = ψ * φ := by
  have h1 := hφ.mul hψ
  have h2 := hψ.mul hφ
  have hinv : Ni * Mi = Mi * Ni := by
    have e1 : (Ni * Mi) * (M * N) = 1 := h1.2.1
    have e2 : (N * M) * (Mi * Ni) = 1 := h2.1
    rw [← hMN] at e2
    exact left_inv_eq_right_inv e1 e2
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨h₁, hh₁, hm₁⟩ := h1.2.2 h
  obtain ⟨h₂, hh₂, hm₂⟩ := h2.2.2 h
  have : h₁ = h₂ := suMat_injective (by rw [hm₁, hm₂, hMN, hinv])
  rw [hh₁, hh₂, this]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4
