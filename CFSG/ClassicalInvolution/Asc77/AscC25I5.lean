module

public import CFSG.ClassicalInvolution.Asc77.AscC25I4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I.Sp5

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.C25V
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

variable {F : Type} [Field F]

theorem mat_swapSp :
    mat 2 F (Sp.swapSp : StatedSp 2 F) = spIncl (K := F) (Fin.rev : Fin 2 → Fin 2) := rfl

theorem yMat_comm_g (k : Fin 2) :
    yMat * (mat 2 F (longInv F 2 k * (Sp.swapSp : StatedSp 2 F))) =
      mat 2 F (longInv F 2 k * (Sp.swapSp : StatedSp 2 F)) * yMat := by
  rw [map_mul, mat_longInv, mat_swapSp]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [yMat, rotM, Matrix.mul_apply, spIncl_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      coords]

@[expose] noncomputable def hMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![1, 1; -1, 1] 0 0 ((2 : F)⁻¹ • !![1, 1; -1, 1])

theorem hMat_symp (h2 : (2 : F) ≠ 0) :
    (hMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * gram F 2 * hMat = gram F 2 := by
  rw [hMat, gram, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.fromBlocks] <;> field_simp <;> ring

@[expose] noncomputable def hMat' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![1, -1; 1, 1] 0 0 ((2 : F)⁻¹ • !![1, -1; 1, 1])

theorem hMat'_symp (h2 : (2 : F) ≠ 0) :
    (hMat' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * gram F 2 * hMat' = gram F 2 := by
  rw [hMat', gram, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.fromBlocks] <;> field_simp <;> ring

theorem exists_swapSp_mul_eq (h2 : (2 : F) ≠ 0) (k : Fin 2) :
    ∃ h : StatedSp 2 F, (Sp.swapSp : StatedSp 2 F) * h = h * longInv F 2 k := by
  fin_cases k
  · refine ⟨ofSymplecticMat hMat (hMat_symp h2), ?_⟩
    apply mat_injective
    rw [map_mul, map_mul, mat_longInv, mat_swapSp]
    change (spIncl (K := F) (Fin.rev : Fin 2 → Fin 2)) * hMat = hMat * _
    ext a b
    rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [hMat, Matrix.mul_apply, spIncl_apply, Fintype.sum_sum_type, Fin.sum_univ_two, coords]
  · refine ⟨ofSymplecticMat hMat' (hMat'_symp h2), ?_⟩
    apply mat_injective
    rw [map_mul, map_mul, mat_longInv, mat_swapSp]
    change (spIncl (K := F) (Fin.rev : Fin 2 → Fin 2)) * hMat' = hMat' * _
    ext a b
    rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [hMat', Matrix.mul_apply, spIncl_apply, Fintype.sum_sum_type, Fin.sum_univ_two, coords]

theorem swapSp_mul_self : (Sp.swapSp : StatedSp 2 F) * Sp.swapSp = 1 := by
  apply mat_injective
  rw [map_mul, mat_swapSp, map_one]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, spIncl_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem yEl_pow_four (h2 : (2 : F) ≠ 0) : (yEl h2) ^ 4 = 1 := by
  apply mat_injective
  rw [map_pow, map_one, mat_yEl]
  have : (yMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ 4 = (yMat * yMat) * (yMat * yMat) := by
    simp [pow_succ, mul_assoc]
  rw [this, yMat_pow_four h2]

theorem yEl_sq_not_central (h2 : (2 : F) ≠ 0) :
    (yEl h2) ^ 2 ∉ Subgroup.center (StatedSp 2 F) := by
  intro hc
  rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hc
  obtain ⟨x, hx⟩ := hc
  have h1 : mat 2 F ((yEl h2) ^ 2) = Matrix.scalar _ (x : F) := by
    rw [mat_apply, ← hx, Matrix.GeneralLinearGroup.coe_scalar]
  have h3 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 1)
  rw [map_pow, mat_yEl, pow_two, yMat_sq_apply h2] at h3
  simp at h3

theorem orderOf_map_yEl {Y : Type} [Group Y] (h2 : (2 : F) ≠ 0) (ψ : StatedSp 2 F →* Y)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) : orderOf (ψ (yEl h2)) = 4 := by
  have hf : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ¬ (ψ (yEl h2)) ^ 2 ^ 1 = 1 := by
    intro h
    rw [pow_one, ← map_pow, ← MonoidHom.mem_ker] at h
    exact yEl_sq_not_central h2 (hker h)
  have h2' : (ψ (yEl h2)) ^ 2 ^ (1 + 1) = 1 := by
    rw [← map_pow]
    have : (yEl h2) ^ 2 ^ (1 + 1) = 1 := yEl_pow_four h2
    rw [this, map_one]
  have := orderOf_eq_prime_pow h1 h2'
  simpa using this


end CFSG.ClassicalInvolution.Asc77.C25I.Sp5
