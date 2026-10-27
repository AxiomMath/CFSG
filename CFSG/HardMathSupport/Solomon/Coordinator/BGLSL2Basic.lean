module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix

variable {E : Type} [Field E]

@[expose] def sl2x (a : E) : SpecialLinearGroup (Fin 2) E :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2y (a : E) : SpecialLinearGroup (Fin 2) E :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

theorem sl2x_coe (a : E) : ((sl2x a : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
    !![1, a; 0, 1] := rfl

theorem sl2y_coe (a : E) : ((sl2y a : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
    !![1, 0; a, 1] := rfl

theorem sl2x_mul (a b : E) : sl2x a * sl2x b = sl2x (a + b) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2x_coe, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2y_mul (a b : E) : sl2y a * sl2y b = sl2y (a + b) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2y_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2x_zero : sl2x (0 : E) = 1 := by
  apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2x_coe]

theorem sl2y_zero : sl2y (0 : E) = 1 := by
  apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2y_coe]

theorem sl2x_pow (a : E) (n : ℕ) : sl2x a ^ n = sl2x (n * a) := by
  induction n with
  | zero => simp [sl2x_zero]
  | succ n ih =>
    rw [pow_succ, ih, sl2x_mul]
    have : (n : E) * a + a = ((n + 1 : ℕ) : E) * a := by push_cast; ring
    rw [this]

theorem sl2y_pow (a : E) (n : ℕ) : sl2y a ^ n = sl2y (n * a) := by
  induction n with
  | zero => simp [sl2y_zero]
  | succ n ih =>
    rw [pow_succ, ih, sl2y_mul]
    have : (n : E) * a + a = ((n + 1 : ℕ) : E) * a := by push_cast; ring
    rw [this]

theorem sl2_sq (g : SpecialLinearGroup (Fin 2) E) :
    (g : Matrix (Fin 2) (Fin 2) E) * g =
      (g : Matrix (Fin 2) (Fin 2) E).trace • (g : Matrix (Fin 2) (Fin 2) E) - 1 := by
  have hd := g.2
  rw [Matrix.det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination (-1 : E) * hd

theorem sl2_scalar_or {M : Matrix (Fin 2) (Fin 2) E} (hdet : M.det = 1) {u w : E}
    (h : u • M = w • (1 : Matrix (Fin 2) (Fin 2) E)) : u = 0 ∨ M.trace ^ 2 = 4 := by
  by_cases hu : u = 0
  · exact Or.inl hu
  right
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne, Matrix.one_apply_eq, ne_eq,
    Fin.zero_eq_one_iff, not_false_eq_true, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, mul_zero, mul_one] at h01 h10 h00 h11
  have h01' : M 0 1 = 0 := (mul_eq_zero.1 h01).resolve_left hu
  have h10' : M 1 0 = 0 := (mul_eq_zero.1 h10).resolve_left hu
  have hdd : M 0 0 = M 1 1 := mul_left_cancel₀ hu (h00.trans h11.symm)
  rw [Matrix.det_fin_two, h01', h10', ← hdd] at hdet
  rw [Matrix.trace_fin_two, ← hdd]
  linear_combination 4 * hdet

theorem sl2_trace_roots (g : SpecialLinearGroup (Fin 2) E) {n : ℕ}
    (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) (hc : g ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) E)) :
    (g : Matrix (Fin 2) (Fin 2) E).trace = 0 ∨ (g : Matrix (Fin 2) (Fin 2) E).trace ^ 2 = 1 ∨
      (g : Matrix (Fin 2) (Fin 2) E).trace ^ 2 = 2 ∨ (g : Matrix (Fin 2) (Fin 2) E).trace ^ 2 = 4 ∨
      (g : Matrix (Fin 2) (Fin 2) E).trace ^ 2 - (g : Matrix (Fin 2) (Fin 2) E).trace - 1 = 0 ∨
      (g : Matrix (Fin 2) (Fin 2) E).trace ^ 2 + (g : Matrix (Fin 2) (Fin 2) E).trace - 1 = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  set M := (g : Matrix (Fin 2) (Fin 2) E) with hM
  set t := M.trace with ht
  have hdet : M.det = 1 := g.2
  have hpow : M ^ n = r • (1 : Matrix (Fin 2) (Fin 2) E) := by
    rw [hM, ← Matrix.SpecialLinearGroup.coe_pow, ← hr, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have h2 : M * M = t • M - 1 := sl2_sq g
  have h3 : M * (M * M) = (t ^ 2 - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) E) := by
    rw [h2, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, h2]
    module
  have h4 : M * (M * (M * M)) =
      (t ^ 3 - 2 * t) • M - (t ^ 2 - 1) • (1 : Matrix (Fin 2) (Fin 2) E) := by
    rw [h3, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, h2]
    module
  have h5 : M * (M * (M * (M * M))) =
      (t ^ 4 - 3 * t ^ 2 + 1) • M - (t ^ 3 - 2 * t) • (1 : Matrix (Fin 2) (Fin 2) E) := by
    rw [h4, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, h2]
    module
  rcases hn with rfl | rfl | rfl | rfl
  · have e : t • M = (r + 1) • (1 : Matrix (Fin 2) (Fin 2) E) := by
      have : M * M = r • (1 : Matrix (Fin 2) (Fin 2) E) := by simpa [pow_two] using hpow
      rw [h2] at this
      have := congrArg (· + (1 : Matrix (Fin 2) (Fin 2) E)) this
      simp only [sub_add_cancel] at this
      rw [this]; module
    rcases sl2_scalar_or hdet e with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have e : (t ^ 2 - 1) • M = (r + t) • (1 : Matrix (Fin 2) (Fin 2) E) := by
      have : M * (M * M) = r • (1 : Matrix (Fin 2) (Fin 2) E) := by
        simpa [pow_succ, Matrix.mul_assoc] using hpow
      rw [h3] at this
      have := congrArg (· + t • (1 : Matrix (Fin 2) (Fin 2) E)) this
      simp only [sub_add_cancel] at this
      rw [this]; module
    rcases sl2_scalar_or hdet e with h | h
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have e : (t ^ 3 - 2 * t) • M = (r + (t ^ 2 - 1)) • (1 : Matrix (Fin 2) (Fin 2) E) := by
      have : M * (M * (M * M)) = r • (1 : Matrix (Fin 2) (Fin 2) E) := by
        simpa [pow_succ, Matrix.mul_assoc] using hpow
      rw [h4] at this
      have := congrArg (· + (t ^ 2 - 1) • (1 : Matrix (Fin 2) (Fin 2) E)) this
      simp only [sub_add_cancel] at this
      rw [this]; module
    rcases sl2_scalar_or hdet e with h | h
    · have : t * (t ^ 2 - 2) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl (by linear_combination h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have e : (t ^ 4 - 3 * t ^ 2 + 1) • M = (r + (t ^ 3 - 2 * t)) • (1 : Matrix (Fin 2) (Fin 2) E) := by
      have : M * (M * (M * (M * M))) = r • (1 : Matrix (Fin 2) (Fin 2) E) := by
        simpa [pow_succ, Matrix.mul_assoc] using hpow
      rw [h5] at this
      have := congrArg (· + (t ^ 3 - 2 * t) • (1 : Matrix (Fin 2) (Fin 2) E)) this
      simp only [sub_add_cancel] at this
      rw [this]; module
    rcases sl2_scalar_or hdet e with h | h
    · have : (t ^ 2 - t - 1) * (t ^ 2 + t - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem pow_p_sq_of_quadratic {p : ℕ} [Fact p.Prime] [CharP E p] (a b : ℤ) {t : E}
    (h : t ^ 2 = a * t + b) : t ^ (p ^ 2) = t := by
  have hu : (t ^ p) ^ 2 = a * t ^ p + b := by
    have := congrArg (frobenius E p) h
    rw [map_pow, map_add, map_mul, map_intCast, map_intCast] at this
    simpa only [frobenius_def] using this
  have hfac : (t ^ p - t) * (t ^ p + t - a) = 0 := by
    linear_combination hu - h
  have hp2 : t ^ (p ^ 2) = (t ^ p) ^ p := by rw [← pow_mul, sq]
  rw [hp2]
  rcases mul_eq_zero.1 hfac with h1 | h1
  · have : t ^ p = t := sub_eq_zero.1 h1
    rw [this]; exact this
  · have h2 : t ^ p = a - t := by linear_combination h1
    rw [h2]
    have h3 : ((a : E) - t) ^ p = (a : E) - t ^ p := by
      have := map_sub (frobenius E p) (a : E) t
      simpa only [map_intCast, frobenius_def] using this
    rw [h3, h2]; ring

theorem sl2_comm_ne {κ : E} (hκ : κ ≠ 0) :
    (QuotientGroup.mk (sl2x (1 : E)) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) *
        QuotientGroup.mk (sl2y κ) ≠
      QuotientGroup.mk (sl2y κ) * QuotientGroup.mk (sl2x (1 : E)) := by
  intro h
  have h1 : ((QuotientGroup.mk (sl2x (1 : E) * sl2y κ) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) E)) =
      QuotientGroup.mk (sl2y κ * sl2x (1 : E)) := h
  obtain ⟨w, hwdef⟩ : ∃ w : SpecialLinearGroup (Fin 2) E,
      w = (sl2x (1 : E) * sl2y κ)⁻¹ * (sl2y κ * sl2x (1 : E)) := ⟨_, rfl⟩
  have hw : w ∈ Subgroup.center (SpecialLinearGroup (Fin 2) E) := hwdef ▸ QuotientGroup.eq.1 h1
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hw
  have hyx : sl2y κ * sl2x (1 : E) = (sl2x 1 * sl2y κ) * w := by rw [hwdef, mul_inv_cancel_left]
  have hm := congrArg (fun g : SpecialLinearGroup (Fin 2) E => (g : Matrix (Fin 2) (Fin 2) E)) hyx
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hr, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp [sl2x_coe, sl2y_coe, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  apply hκ
  have hr1 : r = 1 := by linear_combination -e01
  rw [hr1] at e00
  linear_combination -e00

theorem sl2x_inj {a b : E}
    (h : (QuotientGroup.mk (sl2x a) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) =
      QuotientGroup.mk (sl2x b)) : a = b := by
  obtain ⟨w, hwdef⟩ : ∃ w : SpecialLinearGroup (Fin 2) E, w = (sl2x a)⁻¹ * sl2x b := ⟨_, rfl⟩
  have hw : w ∈ Subgroup.center (SpecialLinearGroup (Fin 2) E) := hwdef ▸ QuotientGroup.eq.1 h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hw
  have hyx : sl2x b = sl2x a * w := by rw [hwdef, mul_inv_cancel_left]
  have hm := congrArg (fun g : SpecialLinearGroup (Fin 2) E => (g : Matrix (Fin 2) (Fin 2) E)) hyx
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hr, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp [sl2x_coe] at e00 e01
  have hr1 : r = 1 := e00.symm
  rw [hr1] at e01
  linear_combination -e01

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
