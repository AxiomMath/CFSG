module

public import CFSG.ClassicalGroups.Unitary.Elements
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUExistBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {ι ρ : K ≃+* K}

variable (ρ) in
@[expose] def RatM {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, ρ (A i j) = A i j

theorem ratM_one {n : ℕ} : RatM ρ (1 : Matrix (Fin n) (Fin n) K) := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem ratM_add {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : RatM ρ A) (hB : RatM ρ B) :
    RatM ρ (A + B) := fun i j => by simp [map_add, hA i j, hB i j]

theorem ratM_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : RatM ρ A) (hB : RatM ρ B) :
    RatM ρ (A * B) := by
  intro i j
  rw [Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hA i k, hB k j]

theorem ratM_smul {n : ℕ} {A : Matrix (Fin n) (Fin n) K} {c : K} (hc : ρ c = c) (hA : RatM ρ A) :
    RatM ρ (c • A) := fun i j => by simp [map_mul, hc, hA i j]

theorem ratM_vecMulVec {n : ℕ} {u v : Fin n → K} (hu : Ratv ρ u) (hv : Ratv ρ v) :
    RatM ρ (vecMulVec u v) := fun i j => by simp [vecMulVec_apply, map_mul, hu i, hv j]

theorem ratv_conj (C : UCtx ι ρ) {n : ℕ} {a : Fin n → K} (ha : Ratv ρ a) :
    Ratv ρ (fun i => ι (a i)) := fun i => by rw [C.comm, ha i]

theorem ratM_tvMat (C : UCtx ι ρ) {n : ℕ} {a : Fin n → K} (ha : Ratv ρ a) {c : K}
    (hc : ρ c = c) : RatM ρ (tvMat ι a c) :=
  ratM_add ratM_one (ratM_smul hc (ratM_vecMulVec ha (ratv_conj C ha)))

theorem ratM_eichlerMat (C : UCtx ι ρ) {n : ℕ} {e y : Fin n → K} (he : Ratv ρ e)
    (hy : Ratv ρ y) {c : K} (hc : ρ c = c) : RatM ρ (eichlerMat ι e y c) := by
  have hy' : Ratv ρ (y + c • e) := ratv_add hy (ratv_smul hc he)
  have hne : Ratv ρ (-e) := fun i => by simp [map_neg, he i]
  exact ratM_mul (ratM_add ratM_one (ratM_vecMulVec hy' (ratv_conj C he)))
    (ratM_add ratM_one (ratM_vecMulVec hne (ratv_conj C hy)))

theorem tv_ratM (C : UCtx ι ρ) {n : ℕ} {a : Fin n → K} (ha : Ratv ρ a) {c : K}
    (hc : ρ c = c) (hI : herm ι a a = 0) (ht : c + ι c = 0) :
    RatM ρ (((tv C.ιinv hI ht : SUid ι n).1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  ratM_tvMat C ha hc

theorem eichler_ratM (C : UCtx ι ρ) {n : ℕ} {e y : Fin n → K} (he : Ratv ρ e)
    (hy : Ratv ρ y) {c : K} (hc : ρ c = c) (heI : herm ι e e = 0) (hey : herm ι e y = 0)
    (hcy : c + ι c = -herm ι y y) :
    RatM ρ (((eichler C.ιinv heI hey hcy : SUid ι n).1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) :=
  ratM_eichlerMat C he hy hc

theorem exists_rational_perp (C : UCtx ι ρ) {a : Fin 3 → K} (ha : Ratv ρ a) (ha0 : a ≠ 0)
    (haI : herm ι a a = 0) :
    ∃ y : Fin 3 → K, Ratv ρ y ∧ herm ι a y = 0 ∧ ¬ ∃ l : K, y = l • a := by
  have hI : ι (a 0) * a 0 + ι (a 1) * a 1 + ι (a 2) * a 2 = 0 := by
    simpa [herm, Fin.sum_univ_three] using haI
  have hz : ∀ y : Fin 3 → K, herm ι a y = ι (a 0) * y 0 + ι (a 1) * y 1 + ι (a 2) * y 2 := by
    intro y; simp [herm, Fin.sum_univ_three]
  have hb : Ratv ρ (fun i => ι (a i)) := ratv_conj C ha
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  by_contra hcon
  push Not at hcon
  have step : ∀ y : Fin 3 → K, (∀ i, ρ (y i) = y i) → herm ι a y = 0 → ∃ l, y = l • a :=
    fun y hy hay => hcon y hy hay
  obtain ⟨l₂, h2⟩ := step ![ι (a 1), -ι (a 0), 0]
    (by intro i; fin_cases i <;> simp [hb0, hb1, map_neg]) (by rw [hz]; simp; ring)
  obtain ⟨l₀, h0⟩ := step ![0, ι (a 2), -ι (a 1)]
    (by intro i; fin_cases i <;> simp [hb1, hb2, map_neg]) (by rw [hz]; simp; ring)
  obtain ⟨l₁, h1⟩ := step ![-ι (a 2), 0, ι (a 0)]
    (by intro i; fin_cases i <;> simp [hb0, hb2, map_neg]) (by rw [hz]; simp; ring)
  have e20 := congrFun h2 0
  have e21 := congrFun h2 1
  have e22 := congrFun h2 2
  have e00 := congrFun h0 0
  have e01 := congrFun h0 1
  have e02 := congrFun h0 2
  have e10 := congrFun h1 0
  have e11 := congrFun h1 1
  have e12 := congrFun h1 2
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e20 e21 e22 e00 e01 e02 e10 e11 e12
  have hιz : ∀ x : K, ι x = 0 → x = 0 := fun x hx => by
    simpa [C.ιinv] using congrArg ι hx
  have hnn : ∀ x : K, ι x * x = 0 → x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).elim (hιz x) id
  have hA2 : a 2 = 0 := by
    by_contra h
    have hl : l₂ = 0 := by
      have : l₂ * a 2 = 0 := by linear_combination -e22
      exact (mul_eq_zero.mp this).resolve_right h
    rw [hl, zero_mul] at e20 e21
    have h1' : a 1 = 0 := hιz _ e20
    have h0' : a 0 = 0 := hιz _ (by linear_combination -e21)
    rw [h1', h0'] at hI
    simp at hI
    exact h (hnn _ (by simpa using hI))
  have hA0 : a 0 = 0 := by
    by_contra h
    have hl : l₀ = 0 := by
      have : l₀ * a 0 = 0 := by linear_combination -e00
      exact (mul_eq_zero.mp this).resolve_right h
    rw [hl, zero_mul] at e01 e02
    have h2' : a 2 = 0 := hιz _ (by linear_combination e01)
    have h1' : a 1 = 0 := hιz _ (by linear_combination -e02)
    rw [h2', h1'] at hI
    simp at hI
    exact h (hnn _ (by simpa using hI))
  have hA1 : a 1 = 0 := by
    by_contra h
    have hl : l₁ = 0 := by
      have : l₁ * a 1 = 0 := by linear_combination -e11
      exact (mul_eq_zero.mp this).resolve_right h
    rw [hl, zero_mul] at e10 e12
    have h2' : a 2 = 0 := hιz _ (by linear_combination -e10)
    have h0' : a 0 = 0 := hιz _ e12
    rw [h2', h0'] at hI
    simp at hI
    exact h (hnn _ (by simpa using hI))
  apply ha0
  funext i
  fin_cases i <;> simp [hA0, hA1, hA2]

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
