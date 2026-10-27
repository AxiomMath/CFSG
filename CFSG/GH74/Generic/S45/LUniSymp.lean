module

public import CFSG.GH74.Generic.S45.LUniReal

public section

namespace CFSG.GH74.Generic.S45.Uni

open Matrix

section Symp

variable {k : Type} [Field k] {m : ℕ} (B : Matrix (Fin m) (Fin m) k)

@[expose] noncomputable def bf : (Fin m → k) →ₗ[k] (Fin m → k) →ₗ[k] k := Matrix.toLinearMap₂' k B

theorem bf_apply (x y : Fin m → k) : bf B x y = x ⬝ᵥ (B *ᵥ y) :=
  Matrix.toLinearMap₂'_apply' B x y

variable {B}

theorem bf_antisymm (hB : Bᵀ = -B) (x y : Fin m → k) : bf B y x = -bf B x y := by
  rw [bf_apply, bf_apply, dotProduct_mulVec, ← mulVec_transpose, hB, neg_mulVec, dotProduct_comm]
  simp

theorem bf_self (h2 : (2 : k) ≠ 0) (hB : Bᵀ = -B) (x : Fin m → k) : bf B x x = 0 := by
  have h := bf_antisymm hB x x
  have : (2 : k) * bf B x x = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

theorem matrix_eq_of_bf {M N : Matrix (Fin m) (Fin m) k}
    (h : ∀ x y, x ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ (N *ᵥ y)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec_single_apply', dotProduct_single] using this

@[expose] noncomputable def sympU (u v : Fin m → k) : Matrix (Fin m) (Fin 2) k :=
  Matrix.of fun i j => ![u i, -(v i)] j

@[expose] noncomputable def sympV (B : Matrix (Fin m) (Fin m) k) (u v : Fin m → k) : Matrix (Fin 2) (Fin m) k :=
  Matrix.of fun j i => ![vecMul (v - u) B i, vecMul (v + u) B i] j

@[expose] noncomputable def sympRot (B : Matrix (Fin m) (Fin m) k) (u v : Fin m → k) : Matrix (Fin m) (Fin m) k :=
  1 + sympU u v * sympV B u v

theorem sympV_mulVec (u v z : Fin m → k) :
    sympV B u v *ᵥ z = ![bf B (v - u) z, bf B (v + u) z] := by
  funext j
  fin_cases j
  · change ((v - u) ᵥ* B) ⬝ᵥ z = bf B (v - u) z
    rw [bf_apply, dotProduct_mulVec]
  · change ((v + u) ᵥ* B) ⬝ᵥ z = bf B (v + u) z
    rw [bf_apply, dotProduct_mulVec]

theorem sympU_mulVec (u v : Fin m → k) (w : Fin 2 → k) :
    sympU u v *ᵥ w = w 0 • u - w 1 • v := by
  funext i
  simp [sympU, mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem sympRot_mulVec (u v z : Fin m → k) :
    sympRot B u v *ᵥ z = z + (bf B v z - bf B u z) • u - (bf B v z + bf B u z) • v := by
  rw [sympRot, add_mulVec, one_mulVec, ← mulVec_mulVec, sympV_mulVec, sympU_mulVec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_add, LinearMap.sub_apply,
    LinearMap.add_apply]
  abel

section SympProps

variable (hB : Bᵀ = -B) {u v : Fin m → k} (huv : bf B u v = 1) (h2 : (2 : k) ≠ 0)

include hB huv h2

theorem sympRot_isometry (x y : Fin m → k) :
    bf B (sympRot B u v *ᵥ x) (sympRot B u v *ᵥ y) = bf B x y := by
  have huu : bf B u u = 0 := bf_self h2 hB u
  have hvv : bf B v v = 0 := bf_self h2 hB v
  have hvu : bf B v u = -1 := by rw [bf_antisymm hB u v, huv]
  rw [sympRot_mulVec, sympRot_mulVec]
  have e1 := bf_antisymm hB x u
  have e2 := bf_antisymm hB x v
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, huu, hvv, huv, hvu]
  linear_combination (bf B v y - bf B u y) * e1 - (bf B v y + bf B u y) * e2

theorem sympRot_sq_apply (w : Fin m → k) :
    sympRot B u v *ᵥ (sympRot B u v *ᵥ w) =
      w + (2 * bf B v w) • u - (2 * bf B u w) • v := by
  have huu : bf B u u = 0 := bf_self h2 hB u
  have hvv : bf B v v = 0 := bf_self h2 hB v
  have hvu : bf B v u = -1 := by rw [bf_antisymm hB u v, huv]
  rw [sympRot_mulVec, sympRot_mulVec]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, huu, hvv, huv, hvu]
  module

theorem sympRot_pow_four :
    (sympRot B u v * sympRot B u v) * (sympRot B u v * sympRot B u v) = 1 := by
  have huu : bf B u u = 0 := bf_self h2 hB u
  have hvv : bf B v v = 0 := bf_self h2 hB v
  have hvu : bf B v u = -1 := by rw [bf_antisymm hB u v, huv]
  apply matrix_ext_mulVec
  intro z
  have e1 := sympRot_sq_apply hB huv h2 z
  have e2 := sympRot_sq_apply hB huv h2 (sympRot B u v *ᵥ (sympRot B u v *ᵥ z))
  simp only [← mulVec_mulVec, one_mulVec] at e1 e2 ⊢
  rw [e2, e1]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, huu, hvv, huv, hvu]
  module

theorem sympRot_det : (sympRot B u v).det = 1 := by
  have huu : bf B u u = 0 := bf_self h2 hB u
  have hvv : bf B v v = 0 := bf_self h2 hB v
  have hvu : bf B v u = -1 := by rw [bf_antisymm hB u v, huv]
  rw [sympRot, det_one_add_mul_comm]
  have e0 : sympV B u v *ᵥ u = ![-1, -1] := by
    rw [sympV_mulVec]
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, huu, hvu]
    funext i
    fin_cases i <;> simp
  have e1 : sympV B u v *ᵥ (-v) = ![1, -1] := by
    rw [mulVec_neg, sympV_mulVec]
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, hvv, huv]
    funext i
    fin_cases i <;> simp
  have hmul : ∀ j i, (sympV B u v * sympU u v) i j =
      (sympV B u v *ᵥ fun r => sympU u v r j) i := fun j i => rfl
  have c1 : (fun r => sympU u v r 1) = -v := by
    funext r
    simp [sympU]
  have c0 : (fun r => sympU u v r 0) = u := by
    funext r
    simp [sympU]
  have hVU : 1 + sympV B u v * sympU u v = !![0, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j
    · show ((1 : Matrix (Fin 2) (Fin 2) k) + sympV B u v * sympU u v) 0 0 = !![0, 1; -1, 0] 0 0
      rw [Matrix.add_apply, hmul, c0, e0]
      simp
    · show ((1 : Matrix (Fin 2) (Fin 2) k) + sympV B u v * sympU u v) 0 1 = !![0, 1; -1, 0] 0 1
      rw [Matrix.add_apply, hmul, c1, e1]
      simp
    · show ((1 : Matrix (Fin 2) (Fin 2) k) + sympV B u v * sympU u v) 1 0 = !![0, 1; -1, 0] 1 0
      rw [Matrix.add_apply, hmul, c0, e0]
      simp
    · show ((1 : Matrix (Fin 2) (Fin 2) k) + sympV B u v * sympU u v) 1 1 = !![0, 1; -1, 0] 1 1
      rw [Matrix.add_apply, hmul, c1, e1]
      simp
  rw [hVU, det_fin_two_of]
  ring

theorem sympRot_not_scalar (hm : 3 ≤ m) (l : k) :
    sympRot B u v * sympRot B u v ≠ l • (1 : Matrix (Fin m) (Fin m) k) := by
  have huu : bf B u u = 0 := bf_self h2 hB u
  have hvv : bf B v v = 0 := bf_self h2 hB v
  have hvu : bf B v u = -1 := by rw [bf_antisymm hB u v, huv]
  intro hl
  have hall : ∀ w, sympRot B u v *ᵥ (sympRot B u v *ᵥ w) = l • w := by
    intro w
    rw [mulVec_mulVec, hl, smul_mulVec, one_mulVec]
  let F : (Fin m → k) →ₗ[k] (Fin 2 → k) := LinearMap.pi ![bf B u, bf B v]
  have hlt : Module.finrank k (Fin 2 → k) < Module.finrank k (Fin m → k) := by
    simp only [Module.finrank_fin_fun]
    omega
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := F) hlt)
  have hw1 : bf B u w = 0 := by
    have := congrFun (LinearMap.mem_ker.1 hw) 0
    simpa [F] using this
  have hw2 : bf B v w = 0 := by
    have := congrFun (LinearMap.mem_ker.1 hw) 1
    simpa [F] using this
  have e1 := hall w
  rw [sympRot_sq_apply hB huv h2, hw1, hw2] at e1
  have hl1 : l = 1 := by
    have : (1 - l) • w = 0 := by
      rw [sub_smul, one_smul, ← e1]
      simp
    have := (smul_eq_zero.1 this).resolve_right hw0
    linear_combination -this
  have e2 := hall u
  rw [sympRot_sq_apply hB huv h2, huu, hvu] at e2
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at huv
  have hl2 : l = -1 := by
    have : (l + 1) • u = 0 := by
      rw [add_smul, one_smul, ← e2]
      module
    have := (smul_eq_zero.1 this).resolve_right hu0
    linear_combination this
  rw [hl1] at hl2
  exact h2 (by linear_combination hl2)

theorem sympRot_transpose_mul : (sympRot B u v)ᵀ * B * sympRot B u v = B := by
  apply matrix_eq_of_bf
  intro x y
  have := sympRot_isometry hB huv h2 x y
  rw [bf_apply, bf_apply] at this
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact this

end SympProps

theorem exists_hyp_pair (hm : 1 ≤ m) (hBd : IsUnit B.det) : ∃ u v : Fin m → k, bf B u v = 1 := by
  have hB0 : ∃ i j, B i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : B = 0 := by
      ext i j
      exact hcon i j
    rw [this] at hBd
    have h0 : (0 : Matrix (Fin m) (Fin m) k).det = 0 := by
      have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      exact det_zero
    rw [h0] at hBd
    exact not_isUnit_zero hBd
  obtain ⟨i, j, hij⟩ := hB0
  refine ⟨Pi.single i 1, (B i j)⁻¹ • Pi.single j 1, ?_⟩
  rw [bf_apply, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have : (Pi.single i 1 : Fin m → k) ⬝ᵥ (B *ᵥ (Pi.single j 1 : Fin m → k)) = B i j := by
    rw [single_dotProduct, one_mul, mulVec_single_apply']
  rw [this]
  exact inv_mul_cancel₀ hij

theorem exists_symp_order_four (h2 : (2 : k) ≠ 0) (hm : 3 ≤ m) (hB : Bᵀ = -B)
    (hBd : IsUnit B.det) :
    ∃ R : Matrix (Fin m) (Fin m) k, Rᵀ * B * R = B ∧ R.det = 1 ∧ (∀ l : k, R * R ≠ l • 1) ∧
      R * R * (R * R) = 1 := by
  obtain ⟨u, v, huv⟩ := exists_hyp_pair (B := B) (by omega) hBd
  exact ⟨sympRot B u v, sympRot_transpose_mul hB huv h2, sympRot_det hB huv h2,
    sympRot_not_scalar hB huv h2 hm, sympRot_pow_four hB huv h2⟩

end Symp

section Alt

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem exists_class2_alt (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) K}
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = (-1 : K) • 1) :
    ∃ c : Matrix (Fin n) (Fin n) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
      (∀ l : K, c * c ≠ l • 1) ∧ c * c * (c * c) = 1 ∧ A * c.map h.bar = c * A := by
  classical
  refine exists_class2 h h2 (by omega) (Or.inr rfl) hAu hAA ?_
  intro εF G' hεF hG'T hunit
  have hεF1 : εF = -1 := Subtype.ext (by simpa using hεF)
  rw [hεF1, neg_smul, one_smul] at hG'T
  exact exists_symp_order_four (two_ne_zero_fixedField h h2) hn hG'T hunit

end Alt

end CFSG.GH74.Generic.S45.Uni
