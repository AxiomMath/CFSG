module

public import CFSG.Quasithin.Background.HConj
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.ClassicalGroups.Unitary

open CFSG.Open CFSG.Quasithin.H CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Matrix

variable {K : Type} [Field K]

theorem glAut_mem_statedSU {n q : ℕ} (σ : K ≃+* K) {A : GL (Fin n) K}
    (hA : A ∈ StatedSU n q K) : glAut σ A ∈ StatedSU n q K := by
  induction hA using Subgroup.closure_induction with
  | mem B hB =>
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [coe_glAut]
      have h := RingHom.map_det (σ : K →+* K) (B : Matrix (Fin n) (Fin n) K)
      rw [hB.1, map_one] at h
      simpa [RingHom.mapMatrix_apply] using h.symm
    · rw [coe_glAut]
      have h1 : ((B : Matrix (Fin n) (Fin n) K).map (· ^ q)).map σ =
          ((B : Matrix (Fin n) (Fin n) K).map σ).map (· ^ q) := by
        ext i j
        simp only [Matrix.map_apply, map_pow]
      have h2 : (((B : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ *
          (B : Matrix (Fin n) (Fin n) K)).map σ = 1 := by
        rw [hB.2]
        simp
      rw [Matrix.map_mul, Matrix.transpose_map, h1] at h2
      exact h2
  | one => rw [map_one]; exact one_mem _
  | mul A B hA hB ihA ihB => rw [map_mul]; exact mul_mem ihA ihB
  | inv A hA ihA => rw [map_inv]; exact inv_mem ihA

theorem fieldMap_conj_matAut_eq_glAut {ι : Type} [Fintype ι] [DecidableEq ι] (σ : K ≃+* K)
    (A : GL ι K) : fieldMap σ * matAut A * (fieldMap σ)⁻¹ = matAut (glAut σ A) :=
  toAddMap_injective fun v => by rw [toAddMap_fieldMap_conj, toAddMap_matAut, coe_glAut]

theorem fieldMap_mem_natNorm_statedSU {n q : ℕ} (σ : K ≃+* K) :
    fieldMap (ι := Fin n) σ ∈ natNorm (StatedSU n q K) := by
  have key : ∀ τ : K ≃+* K, ∀ x ∈ natImage (StatedSU n q K),
      fieldMap τ * x * (fieldMap τ)⁻¹ ∈ natImage (StatedSU n q K) := by
    rintro τ _ ⟨⟨A, hA⟩, rfl⟩
    exact ⟨⟨glAut τ A, glAut_mem_statedSU τ hA⟩, (fieldMap_conj_matAut_eq_glAut τ A).symm⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key σ x, fun h => ?_⟩
  simpa [fieldMap_symm, mul_assoc] using key σ.symm _ h

end CFSG.ClassicalGroups.Unitary
