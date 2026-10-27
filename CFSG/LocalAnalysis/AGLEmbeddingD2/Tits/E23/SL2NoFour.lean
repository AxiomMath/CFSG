module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.LinearCombination
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

theorem sl2_trace_fin_two {F : Type} [Field F] (M : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  simp [Matrix.trace]

theorem sl2_mul_self_eq_trace_smul_sub_one {F : Type} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) :
    M * M = (Matrix.trace M) • M - 1 := by
  rw [Matrix.det_fin_two] at hM
  rw [sl2_trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination (-1 : F) * hM | ring1

theorem sl2_mul_self_eq_one_of_pow_four {F : Type} [Field F] [CharP F 2]
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) (h4 : M * M * (M * M) = 1) :
    M * M = 1 := by
  have hc2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hCH := sl2_mul_self_eq_trace_smul_sub_one M hM
  set t : F := Matrix.trace M with ht
  have hA : (t • M - 1) * (t • M - 1) = 1 := by
    rw [← hCH]
    exact h4
  have e : (t • M - 1) * (t • M - 1) = t • t • (M * M) - (t • M + t • M) + 1 := by
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, Matrix.mul_one]
    abel
  rw [e, ← two_smul F (t • M), hc2, zero_smul, sub_zero, hCH] at hA
  have hkey : t • t • (t • M - 1) = 0 := by
    simpa using hA
  have htr := congrArg Matrix.trace hkey
  simp [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, hc2] at htr
  try rw [← ht] at htr
  have ht0 : t = 0 := by simpa using htr
  rw [hCH, ht0, zero_smul, zero_sub, neg_eq_iff_add_eq_zero]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [one_add_one_eq_two, hc2]
  · simp [hij]

theorem sl2_sq_eq_one_of_pow_four {F : Type} [Field F] [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (h : g ^ 4 = 1) : g ^ 2 = 1 := by
  apply Subtype.ext
  have h4 : (g : Matrix (Fin 2) (Fin 2) F) ^ 4 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, sq]
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq] at h4
  exact sl2_mul_self_eq_one_of_pow_four (g : Matrix (Fin 2) (Fin 2) F) g.2 h4

theorem perm_fin_exists_orderOf_four {m : ℕ} (hm : 4 ≤ m) :
    ∃ σ : Equiv.Perm (Fin m), orderOf σ = 4 := by
  let l : List (Fin m) := [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]
  have hnd : l.Nodup := by
    simp [l, List.nodup_cons, Fin.ext_iff]
  refine ⟨List.formPerm l, ?_⟩
  have hlen : ∀ x : Fin m, l ≠ [x] := fun x h => by
    have := congrArg List.length h
    simp [l] at this
  have hcyc : (List.formPerm l).IsCycle := List.isCycle_formPerm hnd (by simp [l])
  rw [hcyc.orderOf, List.support_formPerm_of_nodup l hnd hlen, List.toFinset_card_of_nodup hnd]
  simp [l]

theorem isEmpty_mulEquiv_perm_sl2 {F : Type} [Field F] [CharP F 2] {m : ℕ} (hm : 4 ≤ m) :
    IsEmpty (Equiv.Perm (Fin m) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨σ, hσ⟩ := perm_fin_exists_orderOf_four hm
  have h4 : σ ^ 4 = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  have hφ4 : (φ σ) ^ 4 = 1 := by
    rw [← map_pow, h4, map_one]
  have hφ2 : (φ σ) ^ 2 = 1 := sl2_sq_eq_one_of_pow_four _ hφ4
  have hσ2 : σ ^ 2 = 1 := φ.injective (by rw [map_pow, hφ2, map_one])
  have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hσ2
  rw [hσ] at hdvd
  norm_num at hdvd

end CFSG.AGLEmbeddingD2.Tits.E23

end
