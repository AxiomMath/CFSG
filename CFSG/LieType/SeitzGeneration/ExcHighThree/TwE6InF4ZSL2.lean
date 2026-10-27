module

public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley Matrix

variable {K : Type*} [Field K]

@[expose] def zA : SL2 K := uSL 1 * vSL (-3)

theorem coe_zA : ((zA : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![-2, 1; -3, 1] := by
  rw [zA, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_conj_zA_eq_HSL (ω : Kˣ) (hω : (ω : K) ^ 2 + ω + 1 = 0) (hω1 : (ω : K) ≠ 1) :
    ∃ M : SL2 K, M⁻¹ * zA * M = HSL ω := by
  have hω0 : (ω : K) ≠ 0 := ω.ne_zero
  have hδ : (ω : K) ^ 2 - ω ≠ 0 := by
    intro h
    apply hω1
    have : (ω : K) * ((ω : K) - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h1
    · exact (hω0 h0).elim
    · linear_combination h1
  set δ : K := (ω : K) ^ 2 - ω with hδdef
  have hinv : ((ω⁻¹ : Kˣ) : K) = (ω : K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by linear_combination (↑ω - 1) * hω)
  have hdet : (!![1, δ⁻¹; 2 + (ω : K), (2 + (ω : K) ^ 2) * δ⁻¹] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    rw [show (1 : K) * ((2 + (ω : K) ^ 2) * δ⁻¹) - δ⁻¹ * (2 + (ω : K)) = δ * δ⁻¹ by
      rw [hδdef]; ring]
    exact mul_inv_cancel₀ hδ
  obtain ⟨M, hM⟩ : ∃ M : SL2 K,
      (M : Matrix (Fin 2) (Fin 2) K) = !![1, δ⁻¹; 2 + (ω : K), (2 + (ω : K) ^ 2) * δ⁻¹] :=
    ⟨⟨_, hdet⟩, rfl⟩
  have hcomm : zA * M = M * HSL ω := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_zA, hM]
    simp only [HSL, hinv]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (try field_simp) <;>
      first
        | ring1
        | linear_combination (-1 : K) * hω
        | linear_combination (1 : K) * hω
        | linear_combination (-((ω : K) ^ 2 - ω + 1)) * hω
        | linear_combination ((ω : K) ^ 2 - ω + 1) * hω
        | linear_combination ((ω : K) - 1) * hω
        | linear_combination (1 - (ω : K)) * hω
  refine ⟨M, ?_⟩
  calc M⁻¹ * zA * M = M⁻¹ * (zA * M) := mul_assoc _ _ _
    _ = M⁻¹ * (M * HSL ω) := by rw [hcomm]
    _ = HSL ω := by rw [← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.LieType.SeitzGeneration.ExcHighThree
