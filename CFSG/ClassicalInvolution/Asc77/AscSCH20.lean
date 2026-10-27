module

public import CFSG.ClassicalInvolution.Asc77.AscSCH18
public import CFSG.ClassicalInvolution.Asc77.AscSCH08
public import CFSG.ClassicalInvolution.Asc77.AscSCH07
public import CFSG.ClassicalInvolution.WeakCT.Blocks

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem coe_blockSL_four_zero (A : SL(2, K)) :
    ((blockSL K 4 2 0 (by omega) A : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [coe_blockSL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [CFSG.ClassicalInvolution.Phan.blockMat_apply]

theorem coe_blockSL_four_two (A : SL(2, K)) :
    ((blockSL K 4 2 2 (by omega) A : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1] := by
  rw [coe_blockSL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [CFSG.ClassicalInvolution.Phan.blockMat_apply]

@[expose] def swapSL : SL(4, K) :=
  ⟨!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]⟩

theorem swapSL_conj_zero (A : SL(2, K)) :
    swapSL * blockSL K 4 2 0 (by omega) A * swapSL⁻¹ = blockSL K 4 2 2 (by omega) A := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_four_zero,
    coe_blockSL_four_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [swapSL, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapSL_conj_two (A : SL(2, K)) :
    swapSL * blockSL K 4 2 2 (by omega) A * swapSL⁻¹ = blockSL K 4 2 0 (by omega) A := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_four_zero,
    coe_blockSL_four_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [swapSL, Matrix.mul_apply, Fin.sum_univ_four]

theorem factorization_sl4_le_two {q : ℕ} (hq3 : q % 3 = 2) (hq : 2 ≤ q) :
    (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)).factorization 3 ≤
      2 * (q * (q ^ 2 - 1)).factorization 3 := by
  have hqn : ¬ 3 ∣ q := by omega
  have hq1 : ¬ 3 ∣ q - 1 := by omega
  have hq2 : ¬ 3 ∣ q ^ 2 + 1 := by
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega
  have hq3' : ¬ 3 ∣ q ^ 2 + q + 1 := by
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega
  have hq1' : 1 ≤ q := by omega
  have d2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [hq1', Nat.one_le_pow 2 q hq1']
    ring
  have d3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    zify [hq1', Nat.one_le_pow 3 q hq1']
    ring
  have d4 : q ^ 4 - 1 = (q - 1) * ((q + 1) * (q ^ 2 + 1)) := by
    zify [hq1', Nat.one_le_pow 4 q hq1']
    ring
  have n1 : q - 1 ≠ 0 := by omega
  have n2 : q + 1 ≠ 0 := by omega
  have n3 : q ^ 2 + q + 1 ≠ 0 := by positivity
  have n4 : q ^ 2 + 1 ≠ 0 := by positivity
  have n5 : q ≠ 0 := by omega
  rw [d2, d3, d4, fac_mul (by positivity) (by positivity), fac_mul (by positivity) (by positivity),
    fac_mul (by positivity) (by positivity), fac_mul n1 n2, fac_mul n1 n3,
    fac_mul n1 (by positivity), fac_mul n2 n4, fac_mul n5 (by positivity), fac_mul n1 n2,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, fac_zero hqn, fac_zero hq1,
    fac_zero hq2, fac_zero hq3']
  omega

section SLtwo

variable {E : Type*} [Group E]

theorem sl_four_perfect_ker_eq_bot_two [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hK : Nat.card K = ℓ ^ f) (h3 : Nat.card K % 3 = 2) [Finite E] [Group.IsPerfect E]
    (π : E →* SL(4, K)) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    rw [hK, Nat.pow_mod] at h3
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h3
    · simp [Nat.zero_pow hf] at h3
  obtain ⟨t, ht⟩ := exists_zpowers_sylow_sl2 hℓ2 hK (r := 3) (by norm_num) (Ne.symm hℓ3)
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  refine ker_eq_bot_of_blocks (by norm_num) π hπ hC hCp (blockSL K 4 2 0 (by omega))
    (blockSL K 4 2 2 (by omega)) (blockSL_injective _) (blockSL_injective _)
    (fun a b => blockSL_comm _ _ (Or.inl (by omega)) a b) ?_ swapSL
    swapSL_conj_zero swapSL_conj_two t ?_
  · intro a b hab
    have hA : a = 1 := by
      have h := congrArg (fun g : SL(4, K) => (g : Matrix (Fin 4) (Fin 4) K)) hab
      simp only [coe_blockSL_four_zero, coe_blockSL_four_two] at h
      have e00 := congrFun (congrFun h 0) 0
      have e01 := congrFun (congrFun h 0) 1
      have e10 := congrFun (congrFun h 1) 0
      have e11 := congrFun (congrFun h 1) 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp_all
    rw [hA, map_one]
  · have hc4 : Nat.card SL(4, K) = Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) *
        (Nat.card K ^ 4 - 1) := by
      rw [Nat.card_congr (specialLinearGroupEquivStatedSL 4 K).toEquiv, card_statedSL_four]
    rw [hc4]
    refine (factorization_sl4_le_two h3 hq).trans ?_
    rw [← card_sl2]
    exact Nat.mul_le_mul_left 2 ht

theorem statedSL_four_perfect_ker_eq_bot_two [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hK : Nat.card K = ℓ ^ f) (h3 : Nat.card K % 3 = 2) [Finite E] [Group.IsPerfect E]
    (π : E →* StatedSL 4 K) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  let e := (specialLinearGroupEquivStatedSL 4 K).symm
  have hker : (e.toMonoidHom.comp π).ker = π.ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  have := sl_four_perfect_ker_eq_bot_two hℓ2 hK h3 (e.toMonoidHom.comp π)
    (e.surjective.comp hπ) (hker ▸ hC) (hker ▸ hCp)
  rwa [hker] at this

end SLtwo

end CFSG.ClassicalInvolution.Asc77.SCH
