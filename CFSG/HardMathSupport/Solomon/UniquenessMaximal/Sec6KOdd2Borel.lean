module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2

open Matrix

variable {L : Type} [Field L]

@[expose] def IsUT (M : Matrix (Fin 3) (Fin 3) L) : Prop := M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

theorem IsUT.mul {M N : Matrix (Fin 3) (Fin 3) L} (hM : IsUT M) (hN : IsUT N) : IsUT (M * N) := by
  obtain ⟨a, b, c⟩ := hM
  obtain ⟨d, e, f⟩ := hN
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, *]

theorem IsUT.one : IsUT (1 : Matrix (Fin 3) (Fin 3) L) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem IsUT.inv {M : Matrix (Fin 3) (Fin 3) L} (h : IsUT M) : IsUT M⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_three]
  obtain ⟨a, b, c⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp [a, b, c]

theorem IsUT.det_eq {M : Matrix (Fin 3) (Fin 3) L} (h : IsUT M) :
    M.det = M 0 0 * M 1 1 * M 2 2 := by
  obtain ⟨a, b, c⟩ := h
  simp [Matrix.det_fin_three, a, b, c]

@[expose] def borel (L : Type) [Field L] : Subgroup (Matrix.GeneralLinearGroup (Fin 3) L) where
  carrier := {g | IsUT (g : Matrix (Fin 3) (Fin 3) L)}
  mul_mem' := fun ha hb => by
    show IsUT ((_ * _ : Matrix.GeneralLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
    rw [Matrix.GeneralLinearGroup.coe_mul]
    exact IsUT.mul ha hb
  one_mem' := by
    show IsUT ((1 : Matrix.GeneralLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
    rw [Matrix.GeneralLinearGroup.coe_one]
    exact IsUT.one
  inv_mem' := fun {g} h => by
    show IsUT ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact IsUT.inv h

theorem mem_borel {g : Matrix.GeneralLinearGroup (Fin 3) L} :
    g ∈ borel L ↔ IsUT (g : Matrix (Fin 3) (Fin 3) L) := Iff.rfl

theorem diag_ne_zero {g : Matrix.GeneralLinearGroup (Fin 3) L} (h : g ∈ borel L) :
    (g : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) L) 2 2 ≠ 0 := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) L).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [IsUT.det_eq h] at hdet
  simp only [ne_eq, mul_eq_zero, not_or] at hdet
  exact ⟨hdet.1.1, hdet.1.2, hdet.2⟩

@[expose] def diagB : borel L →* L × L × L where
  toFun g := ((g.1 : Matrix (Fin 3) (Fin 3) L) 0 0, (g.1 : Matrix (Fin 3) (Fin 3) L) 1 1,
    (g.1 : Matrix (Fin 3) (Fin 3) L) 2 2)
  map_one' := by simp
  map_mul' g h := by
    obtain ⟨a, b, c⟩ := g.2
    obtain ⟨d, e, f⟩ := h.2
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, a, b, c, d, e, f]

def mat3 (a b c x y z : L) : Matrix (Fin 3) (Fin 3) L := !![a, x, y; 0, b, z; 0, 0, c]

theorem mat3_isUT (a b c x y z : L) : IsUT (mat3 a b c x y z) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat3]

theorem det_mat3 (a b c x y z : L) : (mat3 a b c x y z).det = a * b * c := by
  simp [mat3, Matrix.det_fin_three]

noncomputable def borelOfData (a b c : Lˣ) (x y z : L) : borel L :=
  ⟨Matrix.GeneralLinearGroup.mk'' (mat3 (a : L) b c x y z)
    (by rw [det_mat3]; exact (a.isUnit.mul b.isUnit).mul c.isUnit), by
    show IsUT (mat3 (a : L) b c x y z)
    exact mat3_isUT _ _ _ _ _ _⟩

noncomputable def borelEquiv : borel L ≃ (Lˣ × Lˣ × Lˣ) × (L × L × L) where
  toFun g :=
    ((Units.mk0 _ (diag_ne_zero g.2).1, Units.mk0 _ (diag_ne_zero g.2).2.1,
      Units.mk0 _ (diag_ne_zero g.2).2.2),
      ((g.1 : Matrix (Fin 3) (Fin 3) L) 0 1, (g.1 : Matrix (Fin 3) (Fin 3) L) 0 2,
        (g.1 : Matrix (Fin 3) (Fin 3) L) 1 2))
  invFun p := borelOfData p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2
  left_inv g := by
    obtain ⟨a, b, c⟩ := g.2
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [borelOfData, mat3, a, b, c]
  right_inv p := by
    obtain ⟨⟨a, b, c⟩, x, y, z⟩ := p
    simp [borelOfData, mat3]

theorem diagB_eq_one_iff (g : borel L) :
    diagB g = 1 ↔ (borelEquiv g).1 = 1 := by
  simp [diagB, borelEquiv, Prod.ext_iff, Units.ext_iff]

theorem card_borel [Finite L] :
    Nat.card (borel L) = (Nat.card L - 1) ^ 3 * Nat.card L ^ 3 := by
  rw [Nat.card_congr borelEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_units]
  ring

theorem card_ker_diagB [Finite L] : Nat.card (diagB (L := L)).ker = Nat.card L ^ 3 := by
  have e1 : (diagB (L := L)).ker ≃ {p : (Lˣ × Lˣ × Lˣ) × (L × L × L) // p.1 = 1} :=
    (Equiv.subtypeEquiv borelEquiv (fun g => by
      rw [MonoidHom.mem_ker, diagB_eq_one_iff]))
  have e2 : {p : (Lˣ × Lˣ × Lˣ) × (L × L × L) // p.1 = 1} ≃ L × L × L :=
    { toFun := fun p => p.1.2
      invFun := fun z => ⟨(1, z), rfl⟩
      left_inv := by
        rintro ⟨⟨u, z⟩, hu⟩
        simp only at hu
        subst hu
        rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr (e1.trans e2), Nat.card_prod, Nat.card_prod]
  ring

theorem index_borel [Finite L] :
    (borel L).index = (Nat.card L ^ 2 + Nat.card L + 1) * (Nat.card L + 1) := by
  have : Fintype L := Fintype.ofFinite L
  have hq : 2 ≤ Nat.card L := Finite.one_lt_card
  have h1 := Subgroup.card_mul_index (borel L)
  rw [card_borel, Matrix.card_GL_field (𝔽 := L) 3] at h1
  rw [Nat.card_eq_fintype_card (α := L)] at h1 hq ⊢
  generalize Fintype.card L = q at *
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h1
  have hpos : 0 < (q - 1) ^ 3 * q ^ 3 := by
    apply Nat.mul_pos <;> apply Nat.pow_pos <;> omega
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h1]
  have a1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have a2 : q ≤ q ^ 3 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have a3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  zify [a1, a2, a3, (by omega : 1 ≤ q)]
  ring

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2
