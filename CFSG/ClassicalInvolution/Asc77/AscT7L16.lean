module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

namespace T7L

section Gen

variable {F : Type} [Field F]

noncomputable abbrev tr4 {i j : Fin 4} (h : i ≠ j) (c : F) : SL(4, F) :=
  SpecialLinearGroup.transvection h c

@[expose] noncomputable def Xel (β : F) : SL(4, F) :=
  tr4 (show (0 : Fin 4) ≠ 3 by decide) β * tr4 (show (1 : Fin 4) ≠ 2 by decide) (-β)

@[expose] noncomputable def Yel (β : F) : SL(4, F) :=
  tr4 (show (2 : Fin 4) ≠ 1 by decide) β * tr4 (show (3 : Fin 4) ≠ 0 by decide) (-β)

@[expose] noncomputable def Del (a : F) (ha : a ≠ 0) : SL(4, F) :=
  ⟨Matrix.diagonal ![a, a⁻¹, 1, 1], by
    simp [Matrix.det_diagonal, Fin.prod_univ_four, ha]⟩

theorem coe_Xel (β : F) : ((Xel β : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![1, 0, 0, β; 0, 1, -β, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [Xel, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.single_apply, Matrix.one_apply]

theorem coe_Yel (β : F) : ((Yel β : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, β, 1, 0; -β, 0, 0, 1] := by
  rw [Yel, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.single_apply, Matrix.one_apply]

theorem coe_Del (a : F) (ha : a ≠ 0) : ((Del a ha : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    Matrix.diagonal ![a, a⁻¹, 1, 1] := rfl

theorem Xel_comm_u0 (β : F) : Xel β * u0 F = u0 F * Xel β := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_Xel, coe_u0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem Yel_comm_u0 (β : F) : Yel β * u0 F = u0 F * Yel β := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_Yel, coe_u0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem Del_comm_x0 (a : F) (ha : a ≠ 0) : Del a ha * x0 F = x0 F * Del a ha := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_Del, coe_x0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem Del_mul_Del (a : F) (ha : a ≠ 0) : Del a ha * Del a⁻¹ (inv_ne_zero ha) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Del, coe_Del, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, ha]

theorem Xel_conj (a : F) (ha : a ≠ 0) (β : F) :
    Xel (-a * β) * (Del a ha * Xel β * Del a⁻¹ (inv_ne_zero ha)) =
      tr4 (show (1 : Fin 4) ≠ 2 by decide) (β * (a - a⁻¹)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_Xel, coe_Del,
    SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, ha]
  all_goals first | done | (field_simp; ring)

theorem Yel_conj (a : F) (ha : a ≠ 0) (β : F) :
    Yel (-a⁻¹ * β) * (Del a ha * Yel β * Del a⁻¹ (inv_ne_zero ha)) =
      tr4 (show (2 : Fin 4) ≠ 1 by decide) (β * (a - a⁻¹)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_Yel, coe_Del,
    SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, ha]
  all_goals first | done | (field_simp; ring)

theorem tr4_comm_x0_01 (c : F) :
    tr4 (show (0 : Fin 4) ≠ 1 by decide) c * x0 F =
      x0 F * tr4 (show (0 : Fin 4) ≠ 1 by decide) c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, coe_x0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem tr4_comm_x0_10 (c : F) :
    tr4 (show (1 : Fin 4) ≠ 0 by decide) c * x0 F =
      x0 F * tr4 (show (1 : Fin 4) ≠ 0 by decide) c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, coe_x0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem tr4_comm_x0_23 (c : F) :
    tr4 (show (2 : Fin 4) ≠ 3 by decide) c * x0 F =
      x0 F * tr4 (show (2 : Fin 4) ≠ 3 by decide) c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, coe_x0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem tr4_comm_x0_32 (c : F) :
    tr4 (show (3 : Fin 4) ≠ 2 by decide) c * x0 F =
      x0 F * tr4 (show (3 : Fin 4) ≠ 2 by decide) c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, coe_x0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem fund_le_of_adjacent {H : Subgroup SL(4, F)}
    (h01 : ∀ c : F, tr4 (show (0 : Fin 4) ≠ 1 by decide) c ∈ H)
    (h10 : ∀ c : F, tr4 (show (1 : Fin 4) ≠ 0 by decide) c ∈ H)
    (h12 : ∀ c : F, tr4 (show (1 : Fin 4) ≠ 2 by decide) c ∈ H)
    (h21 : ∀ c : F, tr4 (show (2 : Fin 4) ≠ 1 by decide) c ∈ H)
    (h23 : ∀ c : F, tr4 (show (2 : Fin 4) ≠ 3 by decide) c ∈ H)
    (h32 : ∀ c : F, tr4 (show (3 : Fin 4) ≠ 2 by decide) c ∈ H) :
    ⨆ k : Fin 3, ⨆ s : Bool, fundamentalRootSubgroup 3 F k s ≤ H := by
  refine iSup_le fun k => iSup_le fun s => ?_
  fin_cases k <;> cases s <;> rintro x ⟨c, rfl⟩
  · rw [SpecialLinearGroup.transvectionHom_apply]
    exact h10 _
  · rw [SpecialLinearGroup.transvectionHom_apply]
    exact h01 _
  · rw [SpecialLinearGroup.transvectionHom_apply]
    exact h21 _
  · rw [SpecialLinearGroup.transvectionHom_apply]
    exact h12 _
  · rw [SpecialLinearGroup.transvectionHom_apply]
    exact h32 _
  · rw [SpecialLinearGroup.transvectionHom_apply]
    exact h23 _

theorem exists_ne_inv [Finite F] (h4 : 4 ≤ Nat.card F) : ∃ a : F, a ≠ 0 ∧ a - a⁻¹ ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h1 := hcon a ha
      have h2 : a * a = 1 := by
        field_simp at h1
        linear_combination h1
      rcases mul_self_eq_one_iff.mp h2 with h | h <;> simp [h]
  have := Finset.card_le_card hsub
  have h3 := Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  omega

theorem top_le_centralizer_x0_sup_u0 [Finite F] (h4 : 4 ≤ Nat.card F) :
    (⊤ : Subgroup SL(4, F)) ≤ Subgroup.centralizer ({x0 F} : Set SL(4, F)) ⊔
      Subgroup.centralizer ({u0 F} : Set SL(4, F)) := by
  obtain ⟨a, ha0, ha⟩ := exists_ne_inv (F := F) h4
  set H : Subgroup SL(4, F) := Subgroup.centralizer ({x0 F} : Set SL(4, F)) ⊔
    Subgroup.centralizer ({u0 F} : Set SL(4, F)) with hH
  have hx : ∀ g : SL(4, F), g * x0 F = x0 F * g → g ∈ H := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hu : ∀ g : SL(4, F), g * u0 F = u0 F * g → g ∈ H := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hDa : Del a ha0 ∈ H := hx _ (Del_comm_x0 a ha0)
  have hDa' : Del a⁻¹ (inv_ne_zero ha0) ∈ H := hx _ (Del_comm_x0 _ _)
  have h12 : ∀ c : F, tr4 (show (1 : Fin 4) ≠ 2 by decide) c ∈ H := by
    intro c
    have e := Xel_conj a ha0 (c / (a - a⁻¹))
    rw [div_mul_cancel₀ _ ha] at e
    rw [← e]
    exact H.mul_mem (hu _ (Xel_comm_u0 _))
      (H.mul_mem (H.mul_mem hDa (hu _ (Xel_comm_u0 _))) hDa')
  have h21 : ∀ c : F, tr4 (show (2 : Fin 4) ≠ 1 by decide) c ∈ H := by
    intro c
    have e := Yel_conj a ha0 (c / (a - a⁻¹))
    rw [div_mul_cancel₀ _ ha] at e
    rw [← e]
    exact H.mul_mem (hu _ (Yel_comm_u0 _))
      (H.mul_mem (H.mul_mem hDa (hu _ (Yel_comm_u0 _))) hDa')
  have hall := fund_le_of_adjacent (H := H) (fun c => hx _ (tr4_comm_x0_01 c))
    (fun c => hx _ (tr4_comm_x0_10 c)) h12 h21 (fun c => hx _ (tr4_comm_x0_23 c))
    (fun c => hx _ (tr4_comm_x0_32 c))
  rw [iSup_fundamentalRootSubgroup_eq_top (m := 3) (F := F)] at hall
  exact hall

end Gen

end T7L

end CFSG.ClassicalInvolution.Asc77
