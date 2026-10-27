module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F]

@[expose] def diagSL (a b d : F) (h : a * b * d = 1) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![a, 0, 0; 0, b, 0; 0, 0, d], by simp [Matrix.det_fin_three, h]⟩

@[expose] def shiftSL : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def trSL (x y : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, x; 0, 1, y; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem trSL_mul (x y x' y' : F) : trSL x y * trSL x' y' = trSL (x + x') (y + y') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [trSL, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem trSL_zero : (trSL 0 0 : SpecialLinearGroup (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [trSL]

theorem trSL_inv (x y : F) : (trSL x y)⁻¹ = trSL (-x) (-y) :=
  inv_eq_of_mul_eq_one_right (by rw [trSL_mul]; simp [trSL_zero])

theorem diagSL_mul_trSL (a b d : F) (h : a * b * d = 1) (x y : F) :
    diagSL a b d h * trSL x y = trSL (a / d * x) (b / d * y) * diagSL a b d h := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, trSL, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem shiftSL_mul_transvection {i j : Fin 3} (hij : i ≠ j) (c : F) :
    shiftSL * SpecialLinearGroup.transvection hij c =
      SpecialLinearGroup.transvection (fun h => hij (add_right_cancel h) : i + 1 ≠ j + 1) c *
        shiftSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | (ext a b
       fin_cases a <;> fin_cases b <;>
         simp [shiftSL, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
           Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply])

theorem diagSL_mul_transvectionLike {g : F} (hg0 : g ≠ 0) (hD : g * g * g⁻¹ ^ 2 = 1)
    {T : SpecialLinearGroup (Fin 3) F} {u φ : Fin 3 → F}
    (hT : (T : Matrix (Fin 3) (Fin 3) F) = 1 + Matrix.vecMulVec u φ) (hu2 : u 2 = 0) :
    diagSL g g (g⁻¹ ^ 2) hD * T =
      trSL ((g ^ 3 - 1) * φ 2 * u 0) ((g ^ 3 - 1) * φ 2 * u 1) * T *
        diagSL g g (g⁻¹ ^ 2) hD := by
  have hT' : ∀ i j, (T : Matrix (Fin 3) (Fin 3) F) i j =
      (1 : Matrix (Fin 3) (Fin 3) F) i j + u i * φ j := fun i j => by
    rw [hT]; simp [Matrix.vecMulVec_apply]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hT']
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, trSL, hu2, Matrix.one_apply] <;> field_simp <;> ring

theorem transvection_succ_mem {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hshift : (shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K) {i j : Fin 3} (hij : i ≠ j)
    (h : ∀ c : F, SpecialLinearGroup.transvection hij c ∈ K) (c : F) :
    SpecialLinearGroup.transvection (fun h => hij (add_right_cancel h) : i + 1 ≠ j + 1) c ∈ K := by
  have e : SpecialLinearGroup.transvection (fun h => hij (add_right_cancel h) : i + 1 ≠ j + 1) c =
      shiftSL * SpecialLinearGroup.transvection hij c * shiftSL⁻¹ := by
    rw [eq_comm, mul_inv_eq_iff_eq_mul]
    exact shiftSL_mul_transvection hij c
  rw [e]
  exact K.mul_mem (K.mul_mem hshift (h c)) (K.inv_mem hshift)

theorem eq_top_of_torus_shift_transvection {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (hshift : (shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K) {g : F} (hg0 : g ≠ 0)
    (hg3 : g ^ 3 ≠ 1) {T : SpecialLinearGroup (Fin 3) F} {u φ : Fin 3 → F}
    (hT : (T : Matrix (Fin 3) (Fin 3) F) = 1 + Matrix.vecMulVec u φ) (hu2 : u 2 = 0)
    (hu0 : u 0 ≠ 0) (hu1 : u 1 ≠ 0) (hφ2 : φ 2 ≠ 0) (hTK : T ∈ K) : K = ⊤ := by
  have hD0 : g * g * g⁻¹ ^ 2 = 1 := by field_simp
  have hg3' : g ^ 3 - 1 ≠ 0 := sub_ne_zero.2 hg3
  set w₀ : F := (g ^ 3 - 1) * φ 2 * u 0 with hw₀
  set w₁ : F := (g ^ 3 - 1) * φ 2 * u 1 with hw₁
  have hw0 : w₀ ≠ 0 := mul_ne_zero (mul_ne_zero hg3' hφ2) hu0
  have hw1 : w₁ ≠ 0 := mul_ne_zero (mul_ne_zero hg3' hφ2) hu1
  have hw : trSL w₀ w₁ ∈ K := by
    have key := diagSL_mul_transvectionLike hg0 hD0 hT hu2
    have h : trSL w₀ w₁ =
        diagSL g g (g⁻¹ ^ 2) hD0 * T * (diagSL g g (g⁻¹ ^ 2) hD0)⁻¹ * T⁻¹ := by
      rw [eq_comm, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
      exact key
    rw [h]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hdiag _ _ _ _) hTK) (K.inv_mem (hdiag _ _ _ _)))
      (K.inv_mem hTK)
  let V : AddSubgroup (F × F) :=
    { carrier := {p | trSL p.1 p.2 ∈ K}
      zero_mem' := by simp [trSL_zero]
      add_mem' := fun {a b} ha hb => by simpa [trSL_mul] using K.mul_mem ha hb
      neg_mem' := fun {a} ha => by simpa [trSL_inv] using K.inv_mem ha }
  have hmemV : ∀ p : F × F, p ∈ V ↔ trSL p.1 p.2 ∈ K := fun p => Iff.rfl
  have hscale : ∀ p ∈ V, ∀ ρ k : F, ρ ≠ 0 → k ≠ 0 → (ρ * p.1, k ^ 3 / ρ * p.2) ∈ V := by
    intro p hp ρ k hρ hk
    have hδ : ρ / k * (k ^ 2 / ρ) * (1 / k) = 1 := by field_simp
    have h := diagSL_mul_trSL (ρ / k) (k ^ 2 / ρ) (1 / k) hδ p.1 p.2
    have h1 : ρ / k / (1 / k) = ρ := by field_simp
    have h2 : k ^ 2 / ρ / (1 / k) = k ^ 3 / ρ := by field_simp
    rw [h1, h2] at h
    rw [hmemV]
    have : trSL (ρ * p.1) (k ^ 3 / ρ * p.2) =
        diagSL (ρ / k) (k ^ 2 / ρ) (1 / k) hδ * trSL p.1 p.2 *
          (diagSL (ρ / k) (k ^ 2 / ρ) (1 / k) hδ)⁻¹ := by
      rw [h, mul_inv_cancel_right]
    show trSL (ρ * p.1) (k ^ 3 / ρ * p.2) ∈ K
    rw [this]
    exact K.mul_mem (K.mul_mem (hdiag _ _ _ _) hp) (K.inv_mem (hdiag _ _ _ _))
  have hwV : (w₀, w₁) ∈ V := hw
  have hx0 : ((1 - g ^ 3) * w₀, 0) ∈ V := by
    have h1 := hscale _ hwV (-g ^ 3) g (neg_ne_zero.2 (pow_ne_zero 3 hg0)) hg0
    have h2 := V.add_mem hwV h1
    have : ((w₀, w₁) + (-g ^ 3 * (w₀, w₁).1, g ^ 3 / -g ^ 3 * (w₀, w₁).2) : F × F) =
        ((1 - g ^ 3) * w₀, 0) := by
      ext
      · simp only [Prod.fst_add]; ring
      · simp only [Prod.snd_add]
        have : g ^ 3 / -g ^ 3 = -1 := by field_simp
        rw [this]; ring
    rwa [this] at h2
  have hy0 : (0, (1 - g ^ 3) * w₁) ∈ V := by
    have h1 := hscale _ hwV (-1) g (by norm_num) hg0
    have h2 := V.add_mem hwV h1
    have : ((w₀, w₁) + (-1 * (w₀, w₁).1, g ^ 3 / -1 * (w₀, w₁).2) : F × F) =
        (0, (1 - g ^ 3) * w₁) := by
      ext
      · simp only [Prod.fst_add]; ring
      · simp only [Prod.snd_add]; ring
    rwa [this] at h2
  have ha0 : (1 - g ^ 3) * w₀ ≠ 0 := mul_ne_zero (sub_ne_zero.2 (Ne.symm hg3)) hw0
  have hb0 : (1 - g ^ 3) * w₁ ≠ 0 := mul_ne_zero (sub_ne_zero.2 (Ne.symm hg3)) hw1
  have hX : ∀ x : F, trSL x 0 ∈ K := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [trSL_zero]
    · have := hscale _ hx0 (x / ((1 - g ^ 3) * w₀)) 1 (div_ne_zero hx ha0) one_ne_zero
      simp only [mul_zero] at this
      rwa [div_mul_cancel₀ _ ha0] at this
  have hY : ∀ y : F, trSL 0 y ∈ K := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [trSL_zero]
    · have := hscale _ hy0 ((1 - g ^ 3) * w₁ / y) 1 (div_ne_zero hb0 hy) one_ne_zero
      simp only [mul_zero] at this
      have h3 : (1 : F) ^ 3 / ((1 - g ^ 3) * w₁ / y) * ((1 - g ^ 3) * w₁) = y := by
        field_simp
      rwa [h3] at this
  have h02 : ∀ c : F, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c ∈ K := by
    intro c
    have : SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c = trSL c 0 := by
      apply Subtype.ext
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [trSL, SpecialLinearGroup.transvection_coe]
    rw [this]; exact hX c
  have h12 : ∀ c : F, SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) c ∈ K := by
    intro c
    have : SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) c = trSL 0 c := by
      apply Subtype.ext
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [trSL, SpecialLinearGroup.transvection_coe]
    rw [this]; exact hY c
  have h10 := transvection_succ_mem hshift (by decide : (0 : Fin 3) ≠ 2) h02
  have h21 := transvection_succ_mem hshift (by decide : (0 : Fin 3) + 1 ≠ 2 + 1) h10
  have h20 := transvection_succ_mem hshift (by decide : (1 : Fin 3) ≠ 2) h12
  have h01 := transvection_succ_mem hshift (by decide : (1 : Fin 3) + 1 ≠ 2 + 1) h20
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      SpecialLinearGroup.transvection hij c ∈ K := by
    intro i j hij c
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact h02 c
      | exact h12 c
      | exact h10 c
      | exact h21 c
      | exact h20 c
      | exact h01 c
  have htop : (Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup
      (ι := Fin 3) (F := F)))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact hall t.i t.j t.hij t.c

end CFSG.LieType.SeitzGeneration
