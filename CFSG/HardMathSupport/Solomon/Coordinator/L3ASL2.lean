module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix

section SL2

variable {K : Type} [Field K]

theorem sq_eq_trace_smul_sub_one (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 1) :
    M * M = M.trace • M - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination (-1 : K) * hdet

theorem trace_eq_neg_one_of_pow_three {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    (h3 : M * M * M = 1) (hM : M ≠ 1) : M.trace = -1 := by
  set t := M.trace with ht
  have hsq : M * M = t • M - 1 := sq_eq_trace_smul_sub_one M hdet
  have hcube : M * M * M = (t ^ 2 - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc M * M * M = M * (M * M) := Matrix.mul_assoc _ _ _
      _ = M * (t • M - 1) := by rw [hsq]
      _ = t • (M * M) - M := by rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
      _ = t • (t • M - 1) - M := by rw [hsq]
      _ = (t ^ 2 - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) K) := by module
  have h3o := h3
  by_contra hne
  have hne' : t + 1 ≠ 0 := fun h => hne (by linear_combination h)
  rw [hcube] at h3
  have h4 : (t + 1) • ((t - 1) • M) = (t + 1) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have : (t ^ 2 - 1) • M = (1 : Matrix (Fin 2) (Fin 2) K) + t • (1 : Matrix (Fin 2) (Fin 2) K) :=
      sub_eq_iff_eq_add.1 h3
    calc (t + 1) • ((t - 1) • M) = (t ^ 2 - 1) • M := by module
      _ = _ := by rw [this]; module
  have h5 : (t - 1) • M = 1 := smul_right_injective _ hne' h4
  have ht1 : t - 1 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h5
    have := congrFun (congrFun h5 0) 0
    simp at this
  have hM' : M = (t - 1)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← h5, smul_smul, inv_mul_cancel₀ ht1, one_smul]
  set c := (t - 1)⁻¹ with hc
  rw [hM'] at hdet h3o hM
  have hdet' : c ^ 2 = 1 := by
    rw [Matrix.det_smul, Matrix.det_one] at hdet
    simpa using hdet
  have h3' : c ^ 3 = 1 := by
    have := congrFun (congrFun h3o 0) 0
    simp at this
    linear_combination this
  have hc1 : c = 1 := by
    have : c = c ^ 3 / c ^ 2 := by
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0] at hdet'
        simp at hdet'
      field_simp
    rw [this, h3', hdet']
    simp
  exact hM (by rw [hc1, one_smul])

theorem coe_inv_eq_of_det {y : GL (Fin 2) K} (hdet : ((y : Matrix (Fin 2) (Fin 2) K)).det = 1) :
    ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (y : Matrix (Fin 2) (Fin 2) K).trace • (1 : Matrix (Fin 2) (Fin 2) K) -
        (y : Matrix (Fin 2) (Fin 2) K) := by
  have hsq := sq_eq_trace_smul_sub_one (y : Matrix (Fin 2) (Fin 2) K) hdet
  have : (y : Matrix (Fin 2) (Fin 2) K) *
      ((y : Matrix (Fin 2) (Fin 2) K).trace • (1 : Matrix (Fin 2) (Fin 2) K) -
        (y : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hsq]
    module
  exact Units.inv_eq_of_mul_eq_one_right this

theorem card_le_three_of_elemAbelian_sl2 (h3K : (3 : K) ≠ 0) {E : Subgroup (GL (Fin 2) K)}
    (hE : CFSG.Open.IsElemAbelian 3 E)
    (hdet : ∀ x ∈ E, ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1) :
    Nat.card E ≤ 3 := by
  have hcube : ∀ x ∈ E, x * x * x = 1 := fun x hx => by
    have := hE.2 x hx
    simpa [pow_succ] using this
  have htr : ∀ x ∈ E, x ≠ 1 → ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = -1 :=
    fun x hx hx1 => trace_eq_neg_one_of_pow_three (hdet x hx)
      (by rw [← Units.val_mul, ← Units.val_mul, hcube x hx, Units.val_one])
      (fun h => hx1 (Units.ext h))
  have hcyc : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ∈ Subgroup.zpowers x := by
    intro x hx hx1 y hy
    by_contra hyx
    have hy1 : y ≠ 1 := fun h => hyx (h ▸ one_mem _)
    have hxy : x * y ≠ 1 := fun h => hyx (by
      have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]; exact inv_mem (Subgroup.mem_zpowers x))
    have hxy' : x * y⁻¹ ≠ 1 := fun h => hyx (by
      have : y = x := by
        have := mul_inv_eq_one.1 h
        exact this.symm
      rw [this]; exact Subgroup.mem_zpowers x)
    have t1 := htr x hx hx1
    have t2 := htr y hy hy1
    have t3 := htr (x * y) (E.mul_mem hx hy) hxy
    have t4 := htr (x * y⁻¹) (E.mul_mem hx (E.inv_mem hy)) hxy'
    have hinv := coe_inv_eq_of_det (hdet y hy)
    rw [Units.val_mul] at t3 t4
    rw [hinv] at t4
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
      t3, t1, t2] at t4
    simp only [smul_eq_mul] at t4
    apply h3K
    linear_combination t4
  by_cases hE1 : E = ⊥
  · rw [hE1, Subgroup.card_bot]
    norm_num
  · obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
    have hx1' : (x : GL (Fin 2) K) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hle : E ≤ Subgroup.zpowers (x : GL (Fin 2) K) := fun y hy =>
      hcyc x x.2 hx1' y hy
    have hord : orderOf (x : GL (Fin 2) K) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
      have := hE.2 x x.2
      exact this)
    calc Nat.card E ≤ Nat.card (Subgroup.zpowers (x : GL (Fin 2) K)) := by
          have : Finite (Subgroup.zpowers (x : GL (Fin 2) K)) := by
            exact Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hE.2 x x.2⟩)).ne')
          exact Subgroup.card_le_of_le hle
      _ = orderOf (x : GL (Fin 2) K) := Nat.card_zpowers _
      _ ≤ 3 := Nat.le_of_dvd (by norm_num) hord

end SL2

end CFSG.HardMathSupport.Solomon.Coordinator
