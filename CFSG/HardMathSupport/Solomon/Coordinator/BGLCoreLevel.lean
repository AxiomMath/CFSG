module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreDegree
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem transvection_mem_fixSL3 {i j : Fin 3} (hij : i ≠ j) {c : F} (hc : σ c = c) :
    SpecialLinearGroup.transvection hij c ∈ fixSL3 σ := by
  intro a b
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp [hc]

@[expose] noncomputable def g₁ : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

@[expose] noncomputable def g₂ : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 0, -1; 0, 1, 0; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

@[expose] noncomputable def g₃ : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem g₁_mem : (g₁ : SpecialLinearGroup (Fin 3) F) ∈ fixSL3 σ := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [g₁]

theorem g₂_mem : (g₂ : SpecialLinearGroup (Fin 3) F) ∈ fixSL3 σ := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [g₂]

theorem g₃_mem : (g₃ : SpecialLinearGroup (Fin 3) F) ∈ fixSL3 σ := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [g₃]

theorem g₁_mul (c : F) : g₁ * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c =
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c * g₁ := by
  apply Subtype.ext
  change (!![1, 0, 0; 0, 0, -1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) * (1 + Matrix.single 0 1 c) =
    (1 + Matrix.single 0 2 (c)) * !![1, 0, 0; 0, 0, -1; 0, 1, 0]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem g₂_mul (c : F) : g₂ * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c =
    SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c * g₂ := by
  apply Subtype.ext
  change (!![0, 0, -1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) * (1 + Matrix.single 0 1 c) =
    (1 + Matrix.single 2 1 (c)) * !![0, 0, -1; 0, 1, 0; 1, 0, 0]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem g₃_mul (c : F) : g₃ * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c =
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-c) * g₃ := by
  apply Subtype.ext
  change (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) * (1 + Matrix.single 0 1 c) =
    (1 + Matrix.single 1 0 (-c)) * !![0, -1, 0; 1, 0, 0; 0, 0, 1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem conj_eq_of_mul_eq {G : Type*} [Group G] {g x y : G} (h : g * x = y * g) :
    g * x * g⁻¹ = y := by
  rw [h, mul_inv_cancel_right]

theorem mem_of_conj {G : Type*} [Group G] {H : Subgroup G} {g x y : G} (hg : g ∈ H) (hx : x ∈ H)
    (h : g * x = y * g) : y ∈ H := by
  rw [← conj_eq_of_mul_eq h]
  exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)

section Level

variable {H : Subgroup (SpecialLinearGroup (Fin 3) F)} (hA : fixSL3 σ ≤ H)
include hA

theorem x02_mem_of_x01 {c : F}
    (h : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H :=
  mem_of_conj (hA g₁_mem) h (g₁_mul c)

theorem x21_mem_of_x01 {c : F}
    (h : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H) :
    SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H :=
  mem_of_conj (hA g₂_mem) h (g₂_mul c)

theorem x10_mem_of_x01 {c : F}
    (h : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-c) ∈ H :=
  mem_of_conj (hA g₃_mem) h (g₃_mul c)

theorem top_le_of_x01 [Finite F] (hr : (orderOf σ).Prime) {t : F}
    (ht : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t ∈ H)
    (hσt : σ t ≠ t) : ⊤ ≤ H := by
  set x := fun c : F => SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c
  let R : Subring F :=
    { carrier := {c | x c ∈ H}
      mul_mem' := by
        intro a b ha hb
        have h1 := x02_mem_of_x01 hA ha
        have h2 := x21_mem_of_x01 hA hb
        have hc := H.mul_mem (H.mul_mem (H.mul_mem h1 h2) (H.inv_mem h1)) (H.inv_mem h2)
        rw [← commutatorElement_def,
          Matrix.SpecialLinearGroup.commutatorElement_transvection] at hc
        exact hc
      one_mem' := hA (transvection_mem_fixSL3 _ (map_one σ))
      add_mem' := by
        intro a b ha hb
        change x (a + b) ∈ H
        simp only [x, SpecialLinearGroup.transvection_add]
        exact H.mul_mem ha hb
      zero_mem' := by
        change x 0 ∈ H
        simp only [x, SpecialLinearGroup.transvection_coeff_zero]
        exact H.one_mem
      neg_mem' := by
        intro a ha
        change x (-a) ∈ H
        simp only [x, ← SpecialLinearGroup.transvection_inv]
        exact H.inv_mem ha }
  have hR : ∀ c, x c ∈ H := fun c =>
    subring_eq_top_of_not_fixed hr (R := R)
      (fun y hy => hA (transvection_mem_fixSL3 _ hy)) ht hσt c
  have h02 : ∀ c, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H :=
    fun c => x02_mem_of_x01 hA (hR c)
  have h21 : ∀ c, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H :=
    fun c => x21_mem_of_x01 hA (hR c)
  have h10 : ∀ c, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ H := by
    intro c
    have := x10_mem_of_x01 hA (hR (-c))
    rwa [neg_neg] at this
  have hcomm : ∀ {i j l : Fin 3} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l),
      (∀ c, SpecialLinearGroup.transvection hij c ∈ H) →
      (∀ c, SpecialLinearGroup.transvection hjl c ∈ H) →
      ∀ c, SpecialLinearGroup.transvection hil c ∈ H := by
    intro i j l hij hjl hil hi hj c
    have h := H.mul_mem (H.mul_mem (H.mul_mem (hi c) (hj 1)) (H.inv_mem (hi c)))
      (H.inv_mem (hj 1))
    rw [← commutatorElement_def, Matrix.SpecialLinearGroup.commutatorElement_transvection,
      mul_one] at h
    exact h
  have h12 : ∀ c, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ H :=
    hcomm (show (1 : Fin 3) ≠ 0 by decide) (show (0 : Fin 3) ≠ 2 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) h10 h02
  have h20 : ∀ c, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ H :=
    hcomm (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) h21 h10
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F), SpecialLinearGroup.transvection hij c ∈ H := by
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hR c
    · exact h02 c
    · exact h10 c
    · exact absurd rfl hij
    · exact h12 c
    · exact h20 c
    · exact h21 c
    · exact absurd rfl hij
  rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  exact hall i j hij c

theorem top_le_of_x02 [Finite F] (hr : (orderOf σ).Prime) {t : F}
    (ht : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t ∈ H)
    (hσt : σ t ≠ t) : ⊤ ≤ H := by
  have h : g₁⁻¹ * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t * g₁⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, g₁_mul, mul_assoc, mul_inv_cancel, mul_one]
  exact top_le_of_x01 hA hr (mem_of_conj (H.inv_mem (hA g₁_mem)) ht h) hσt

theorem top_le_of_x12 [Finite F] (hr : (orderOf σ).Prime) {t : F}
    (ht : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t ∈ H)
    (hσt : σ t ≠ t) : ⊤ ≤ H := by
  have hg : g₃ * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t * g₃ := by
    apply Subtype.ext
    change (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
        (1 + Matrix.single 0 2 t) = (1 + Matrix.single 1 2 t) * !![0, -1, 0; 1, 0, 0; 0, 0, 1]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  have h : g₃⁻¹ * SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t * g₃⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hg, mul_assoc, mul_inv_cancel, mul_one]
  exact top_le_of_x02 hA hr (mem_of_conj (H.inv_mem (hA g₃_mem)) ht h) hσt

end Level

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
