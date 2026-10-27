module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsRad

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type*} [Field F] [Finite F]

theorem mem_uFiveRow_iff_row {x : unitriangular 5 F} :
    x ∈ uFiveRow ↔ ∀ i j : Fin 5, i ≠ 0 → i ≠ j → ypsMat x i j = 0 := by
  rw [mem_uFiveRow]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ i j hi hij
    rcases lt_or_gt_of_ne hij with h | h
    · fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hi
        | exact absurd h (by decide)
        | assumption
    · exact ypsMat_apply_of_lt x h
  · intro h
    exact ⟨h 1 2 (by decide) (by decide), h 1 3 (by decide) (by decide),
      h 1 4 (by decide) (by decide), h 2 3 (by decide) (by decide), h 2 4 (by decide) (by decide),
      h 3 4 (by decide) (by decide)⟩

theorem uFiveRow_sub_one_mul {x y : unitriangular 5 F} (hx : x ∈ uFiveRow) (hy : y ∈ uFiveRow) :
    (ypsMat x - 1) * (ypsMat y - 1) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := hy
  rw [ypsMat_eq x, ypsMat_eq y, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_five]

theorem uFiveRow_comm {x y : unitriangular 5 F} (hx : x ∈ uFiveRow) (hy : y ∈ uFiveRow) :
    x * y = y * x := by
  apply ypsMat_injective
  have h1 := uFiveRow_sub_one_mul hx hy
  have h2 := uFiveRow_sub_one_mul hy hx
  rw [ypsMat_mul, ypsMat_mul]
  have e : ∀ A B : Matrix (Fin 5) (Fin 5) F, A * B = (A - 1) * (B - 1) + A + B - 1 := by
    intro A B
    noncomm_ring
  rw [e, e (ypsMat y), h1, h2]
  abel

theorem conj_mem_uFiveRow {x : unitriangular 5 F} (hx : x ∈ uFiveRow) (g : unitriangular 5 F) :
    g * x * g⁻¹ ∈ uFiveRow := by
  rw [mem_uFiveRow_iff_row] at hx ⊢
  intro i j hi hij
  have hGX : ∀ l, (ypsMat g * ypsMat x) i l = ypsMat g i l := fun l => by
    rw [Matrix.mul_apply, Finset.sum_eq_single l]
    · rw [ypsMat_apply_self, mul_one]
    · intro k _ hkl
      by_cases hk : k = 0
      · subst hk
        rw [ypsMat_apply_of_lt g (Fin.pos_iff_ne_zero.2 hi), zero_mul]
      · rw [hx k l hk hkl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h
  rw [ypsMat_mul, ypsMat_mul, Matrix.mul_apply]
  simp_rw [hGX]
  rw [← Matrix.mul_apply, ← ypsMat_mul, mul_inv_cancel, ypsMat_one, Matrix.one_apply_ne hij]

theorem uFiveRoot_mem_uFiveRow {j : Fin 5} (hj : 0 < j) (a : F) :
    uFiveRoot 0 j hj a ∈ uFiveRow := by
  rw [mem_uFiveRow_iff_row]
  intro i k hi _
  rw [ypsMat_uFiveRoot, Matrix.add_apply, Matrix.one_apply_ne (by assumption),
    Matrix.single_apply_of_row_ne (Ne.symm hi), add_zero]

theorem mem_uFiveRow_of_comm {g : unitriangular 5 F} (h : ∀ x ∈ uFiveRow, g * x = x * g) :
    g ∈ uFiveRow := by
  have h1 := h _ (uFiveRoot_mem_uFiveRow (j := 1) (by decide) 1)
  have h2 := h _ (uFiveRoot_mem_uFiveRow (j := 2) (by decide) 1)
  have h3 := h _ (uFiveRoot_mem_uFiveRow (j := 3) (by decide) 1)
  have e : ∀ {j : Fin 5} (hj : 0 < j), g * uFiveRoot 0 j hj 1 = uFiveRoot 0 j hj 1 * g →
      ∀ l, l ≠ j → ypsMat g j l = 0 := by
    intro j hj hg l hl
    have e1 := congrArg (fun u => ypsMat u 0 l) hg
    simp only [ypsMat_mul, ypsMat_uFiveRoot, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.add_apply, mul_single_one_apply_five, single_one_mul_apply_five] at e1
    simpa [hl, ypsMat_apply_of_lt g hj] using e1
  exact ⟨e _ h1 2 (by decide), e _ h1 3 (by decide), e _ h1 4 (by decide), e _ h2 3 (by decide),
    e _ h2 4 (by decide), e _ h3 4 (by decide)⟩


theorem uFiveRow_mul_self [CharP F 2] {x : unitriangular 5 F} (hx : x ∈ uFiveRow) :
    x * x = 1 := by
  have h := uFiveRow_sub_one_mul hx hx
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  apply ypsMat_injective
  rw [ypsMat_mul, ypsMat_one]
  have e : ypsMat x * ypsMat x =
      (ypsMat x - 1) * (ypsMat x - 1) + (2 : F) • (ypsMat x - 1) + 1 := by
    rw [two_smul]
    noncomm_ring
  rw [e, h, h2, zero_smul, zero_add, zero_add]

@[expose] def uFiveRowMat (a : Fin 4 → F) : Matrix (Fin 5) (Fin 5) F :=
  !![0, a 0, a 1, a 2, a 3; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]

omit [Finite F] in
theorem isStrictUpperFive_uFiveRowMat (a : Fin 4 → F) : IsStrictUpperFive (uFiveRowMat a) :=
  isStrictUpperFive_of_eq rfl

@[expose] noncomputable def uFiveRowEquiv : (Fin 4 → F) ≃ uFiveRow (F := F) where
  toFun a := ⟨uFiveElt (uFiveRowMat a) (isStrictUpperFive_uFiveRowMat a), by
    rw [mem_uFiveRow, ypsMat_uFiveElt]
    simp [uFiveRowMat]⟩
  invFun x := ![ypsMat (x : unitriangular 5 F) 0 1, ypsMat (x : unitriangular 5 F) 0 2,
    ypsMat (x : unitriangular 5 F) 0 3, ypsMat (x : unitriangular 5 F) 0 4]
  left_inv a := by
    ext k
    fin_cases k <;> simp [ypsMat_uFiveElt, uFiveRowMat]
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
    apply Subtype.ext
    apply ypsMat_injective
    change 1 + uFiveRowMat _ = ypsMat x
    conv_rhs => rw [ypsMat_eq x, h1, h2, h3, h4, h5, h6]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uFiveRowMat]

theorem card_uFiveRow : Nat.card (uFiveRow (F := F)) = Nat.card F ^ 4 := by
  rw [← Nat.card_congr (uFiveRowEquiv (F := F)), Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 4),
    Fintype.card_fin]

@[expose] noncomputable def uFiveRowScalar (t : F) (ht : t ≠ 0) :
    uFiveRow (F := F) ≃* uFiveRow (F := F) where
  toFun x := ⟨uFiveElt (t • (ypsMat (x : unitriangular 5 F) - 1))
      ((isStrictUpperFive_ypsMat_sub_one _).smul t), by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := x.2
    rw [mem_uFiveRow, ypsMat_uFiveElt]
    simp [h1, h2, h3, h4, h5, h6]⟩
  invFun x := ⟨uFiveElt (t⁻¹ • (ypsMat (x : unitriangular 5 F) - 1))
      ((isStrictUpperFive_ypsMat_sub_one _).smul t⁻¹), by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := x.2
    rw [mem_uFiveRow, ypsMat_uFiveElt]
    simp [h1, h2, h3, h4, h5, h6]⟩
  left_inv x := Subtype.ext (ypsMat_injective (by
    simp only [ypsMat_uFiveElt, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
    abel))
  right_inv x := Subtype.ext (ypsMat_injective (by
    simp only [ypsMat_uFiveElt, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht, one_smul]
    abel))
  map_mul' x y := Subtype.ext (ypsMat_injective (by
    have hp := uFiveRow_sub_one_mul x.2 y.2
    change 1 + t • (ypsMat (x : unitriangular 5 F) * ypsMat (y : unitriangular 5 F) - 1) =
      (1 + t • (ypsMat (x : unitriangular 5 F) - 1)) *
        (1 + t • (ypsMat (y : unitriangular 5 F) - 1))
    have e : ypsMat (x : unitriangular 5 F) * ypsMat (y : unitriangular 5 F) - 1 =
        (ypsMat (x : unitriangular 5 F) - 1) * (ypsMat (y : unitriangular 5 F) - 1) +
          (ypsMat (x : unitriangular 5 F) - 1) + (ypsMat (y : unitriangular 5 F) - 1) := by
      noncomm_ring
    rw [e, hp, zero_add, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Matrix.smul_mul,
      Matrix.mul_smul, hp, smul_zero, smul_zero, smul_add]
    abel))

theorem ypsMat_uFiveRowScalar (t : F) (ht : t ≠ 0) (x : uFiveRow (F := F)) :
    ypsMat ((uFiveRowScalar t ht x : uFiveRow (F := F)) : unitriangular 5 F) =
      1 + t • (ypsMat (x : unitriangular 5 F) - 1) := rfl

theorem uFiveRowScalar_conj (t : F) (ht : t ≠ 0) (g : unitriangular 5 F) (x y : uFiveRow (F := F))
    (hxy : (y : unitriangular 5 F) = g * x * g⁻¹) :
    ((uFiveRowScalar t ht y : uFiveRow (F := F)) : unitriangular 5 F) =
      g * (uFiveRowScalar t ht x : uFiveRow (F := F)) * g⁻¹ := by
  apply ypsMat_injective
  have hgg : ypsMat g * ypsMat g⁻¹ = 1 := by rw [← ypsMat_mul, mul_inv_cancel, ypsMat_one]
  rw [ypsMat_uFiveRowScalar, hxy, ypsMat_mul, ypsMat_mul, ypsMat_mul, ypsMat_mul,
    ypsMat_uFiveRowScalar]
  rw [mul_add, add_mul, mul_one, hgg, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_one,
    hgg]

theorem uFiveRowScalar_eq_self (t : F) (ht : t ≠ 0) (ht1 : t ≠ 1) (x : uFiveRow (F := F))
    (hx : uFiveRowScalar t ht x = x) : x = 1 := by
  have h := congrArg (fun u : uFiveRow (F := F) => ypsMat (u : unitriangular 5 F)) hx
  simp only [ypsMat_uFiveRowScalar] at h
  have h2 : (t - 1) • (ypsMat (x : unitriangular 5 F) - 1) = 0 := by
    rw [sub_smul, one_smul]
    nth_rewrite 2 [← h]
    abel
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) ht1
  · apply Subtype.ext
    apply ypsMat_injective
    exact (sub_eq_zero.1 h3).trans ypsMat_one.symm

end CFSG.SeitzReduction.LinearPilot
