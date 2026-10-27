module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourE9

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped MatrixGroups

section NatMod

variable {F : Type*} [Field F]

theorem mul_self_eq_one_of_fixed_vec [CharP F 2] {x : SL(2, F)} {v : Fin 2 → F} (hv0 : v ≠ 0)
    (hv : (x : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : x * x = 1 := by
  set M : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = 1 := x.2
  have hsing : (M - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv0, by rw [Matrix.sub_mulVec, hv, Matrix.one_mulVec, sub_self]⟩
  rw [Matrix.det_fin_two] at hdet hsing
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hsing
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have htr : M 0 0 + M 1 1 = 0 := by
    have : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 =
        (M 0 0 * M 1 1 - M 0 1 * M 1 0) - (M 0 0 + M 1 1) + 1 := by ring
    rw [this, hdet] at hsing
    linear_combination -hsing + h2
  have hd : M 1 1 = M 0 0 := by
    linear_combination htr + (-(M 0 0)) * h2
  rw [hd] at hdet htr
  have hMM : M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
    · linear_combination hdet + (M 0 1 * M 1 0) * h2
    · linear_combination (M 0 1) * htr
    · linear_combination (M 1 0) * htr
    · linear_combination hdet + (M 0 1 * M 1 0) * h2
  apply Subtype.ext
  exact hMM

theorem eq_zero_of_fixed_vec_of_odd_order [CharP F 2] {x : SL(2, F)} (hxo : Odd (orderOf x))
    (hx1 : x ≠ 1) {v : Fin 2 → F} (hv : (x : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : v = 0 := by
  by_contra hv0
  have hx2 := mul_self_eq_one_of_fixed_vec hv0 hv
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hxo
      exact absurd hxo (by decide)
  exact hx1 (orderOf_eq_one_iff.mp h1)

@[expose] def slUpper (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def slLower (t : F) : SL(2, F) :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem slUpper_mulVec (t : F) (w : Fin 2 → F) :
    ((slUpper t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = ![w 0 + t * w 1, w 1] := by
  ext i
  fin_cases i <;> simp [slUpper, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem slLower_mulVec (t : F) (w : Fin 2 → F) :
    ((slLower t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = ![w 0, t * w 0 + w 1] := by
  ext i
  fin_cases i <;> simp [slLower, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_smul_of_comm_sl2 (E : (Fin 2 → F) → (Fin 2 → F))
    (hadd : ∀ a b, E (a + b) = E a + E b)
    (hcomm : ∀ (g : SL(2, F)) (w : Fin 2 → F),
      E ((g : Matrix (Fin 2) (Fin 2) F).mulVec w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (E w)) :
    ∃ l : F, ∀ w, E w = l • w := by
  have hU : ∀ (t : F) (w : Fin 2 → F),
      E ![w 0 + t * w 1, w 1] = ![E w 0 + t * E w 1, E w 1] := by
    intro t w
    have := hcomm (slUpper t) w
    rwa [slUpper_mulVec, slUpper_mulVec] at this
  have hL : ∀ (t : F) (w : Fin 2 → F),
      E ![w 0, t * w 0 + w 1] = ![E w 0, t * E w 0 + E w 1] := by
    intro t w
    have := hcomm (slLower t) w
    rwa [slLower_mulVec, slLower_mulVec] at this
  have hvec : ∀ w : Fin 2 → F, w = ![w 0, w 1] := by
    intro w
    ext i
    fin_cases i <;> rfl
  have h1 : E ![1, 0] 1 = 0 := by
    have h := hU 1 ![1, 0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul,
      mul_zero, add_zero] at h
    have h0 := congrFun h 0
    simpa using h0
  have h2 : E ![0, 1] 0 = 0 := by
    have h := hL 1 ![0, 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul,
      mul_zero, zero_add] at h
    have h0 := congrFun h 1
    simpa using h0
  have h3 : ∀ t : F, E ![t, 0] = ![t * E ![0, 1] 1, 0] := by
    intro t
    have h := hU t ![0, 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add,
      mul_one] at h
    have hsplit : (![t, 1] : Fin 2 → F) = ![t, 0] + ![0, 1] := by
      ext i; fin_cases i <;> simp
    rw [hsplit, hadd] at h
    ext i
    fin_cases i
    · have h0 := congrFun h 0
      simp [h2] at h0
      simpa using h0
    · have h0 := congrFun h 1
      simp at h0
      simpa using h0
  have h4 : E ![1, 0] 0 = E ![0, 1] 1 := by
    have h := h3 1
    have h0 := congrFun h 0
    simpa using h0
  set l : F := E ![0, 1] 1 with hl
  have h5 : ∀ t : F, E ![0, t] = ![0, t * l] := by
    intro t
    have h := hL t ![1, 0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one,
      add_zero] at h
    have hsplit : (![1, t] : Fin 2 → F) = ![1, 0] + ![0, t] := by
      ext i; fin_cases i <;> simp
    rw [hsplit, hadd] at h
    have hE1 : E ![1, 0] = ![l, 0] := by
      ext i
      fin_cases i
      · simpa [hl] using h4
      · simpa using h1
    rw [hE1] at h
    ext i
    fin_cases i
    · have h0 := congrFun h 0
      simp at h0
      simpa using h0
    · have h0 := congrFun h 1
      simp at h0
      simpa using h0
  refine ⟨l, fun w => ?_⟩
  have hw : w = ![w 0, 0] + ![0, w 1] := by
    ext i; fin_cases i <;> simp
  rw [hw, hadd, h3, h5]
  ext i
  fin_cases i <;> simp [mul_comm]

end NatMod

end CFSG.CGT.PushingUpLit.CGT6
