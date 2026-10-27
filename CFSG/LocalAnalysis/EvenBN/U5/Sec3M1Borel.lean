module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1GamTwo
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FModel

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem barInvT_upper (c : K) :
    barInvT h (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K) = !![1, 0; h.bar c, 1] := by
  have := h.charP
  have em : (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).map h.bar = !![1, h.bar c; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e : ((!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).map h.bar)⁻¹ = !![1, h.bar c; 0, 1] := by
    refine inv_eq_right_inv ?_
    rw [em]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  rw [barInvT, e]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable (h) in
@[expose] def uSU (c : K) : hypSU h 2 1 := lev (hK := h) !![1, c; 0, 1] (isUnit_det_upper c)

theorem mat_uSU (c : K) :
    mat (uSU h c) = blk3 !![1, c; 0, 1] 0 0 1 0 !![1, 0; h.bar c, 1] := by
  rw [uSU, mat_lev, oddDiag, barInvT_upper, det_fin_two_of]
  congr 1
  ext k l
  fin_cases k
  fin_cases l
  simp

theorem uSU_mem_patSub (c : K) : uSU h c ∈ patSub h sI₁ isPattern_sI₁ := by
  refine mem_patSub_sI₁.2 ⟨lev_upper_mem_U c, ?_⟩
  simp only [mat_uSU]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem uSU_mem_N₁sub (c : K) : uSU h c ∈ N₁sub h := by
  have hdet : (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [det_fin_two_of]
    simp
  refine ⟨⟨!![1, c; 0, 1], hdet⟩, ?_⟩
  rw [← lev_eq_leviSU (⟨!![1, c; 0, 1], hdet⟩ : SpecialLinearGroup (Fin 2) K)
    (by change IsUnit (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).det; rw [hdet]; exact isUnit_one)]
  rfl

theorem mat_uSU_e₁e₂ (c : K) : mat (uSU h c) ιe₁ ιe₂ = c := by
  rw [mat_uSU]
  rfl

theorem uSU_add (a b : K) : uSU h (a + b) = uSU h a * uSU h b := by
  rw [uSU, uSU, uSU, ← lev_mul]
  apply lev_congr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uSU_zero : uSU h 0 = 1 := by
  rw [uSU, ← lev_one (h := h)]
  apply lev_congr
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem uSU_injective : Function.Injective (uSU h) := fun a b e => by
  rw [← mat_uSU_e₁e₂ (h := h) a, ← mat_uSU_e₁e₂ (h := h) b, e]

theorem eq_uSU_of_mem {u : hypSU h 2 1} (hu : u ∈ patSub h sI₁ isPattern_sI₁) :
    u = uSU h (mat u ιe₁ ιe₂) := by
  obtain ⟨hubar, -, -, ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩⟩ := rootI₁_entries hu
  obtain ⟨huU, -⟩ := mem_patSub_sI₁.1 hu
  refine eq_of_U_entries huU (lev_upper_mem_U _) (forall_upper.2 ?_)
  simp only [mat_uSU]
  exact ⟨rfl, a1, a5, a8, a3, a7, a6, a4, a2, hubar⟩

theorem card_patSub_I₁ : Nat.card (patSub h sI₁ isPattern_sI₁) = (2 ^ f) ^ 2 := by
  set φ : K → patSub h sI₁ isPattern_sI₁ := fun c => ⟨uSU h c, uSU_mem_patSub c⟩ with hφ
  have hbij : Function.Bijective φ := by
    refine ⟨fun a b e => uSU_injective (congrArg Subtype.val e), fun u => ?_⟩
    refine ⟨mat (u : hypSU h 2 1) ιe₁ ιe₂, Subtype.ext ?_⟩
    exact (eq_uSU_of_mem u.2).symm
  rw [← Nat.card_eq_of_bijective φ hbij, h.card_eq_sq]

theorem det_diag_units (α : Kˣ) :
    (!![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [det_fin_two_of]
  simp

variable (h) in
@[expose] def dHom : Kˣ →* hypSU h 2 1 where
  toFun α := lev (hK := h) !![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)]
    (by rw [det_diag_units]; exact isUnit_one)
  map_one' := by
    rw [← lev_one (h := h)]
    apply lev_congr
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' α β := by
    rw [← lev_mul]
    apply lev_congr
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem dHom_apply (α : Kˣ) :
    dHom h α = lev (hK := h) !![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)]
      (by rw [det_diag_units]; exact isUnit_one) := rfl

theorem dHom_mem_Isub (α : Kˣ) : dHom h α ∈ Isub h :=
  (lev_diag (h := h) α.ne_zero (α⁻¹).ne_zero).1

theorem dHom_mem_N₁sub (α : Kˣ) : dHom h α ∈ N₁sub h := by
  refine ⟨⟨_, det_diag_units α⟩, ?_⟩
  rw [dHom_apply, ← lev_eq_leviSU (⟨_, det_diag_units α⟩ : SpecialLinearGroup (Fin 2) K)
    (by change IsUnit (!![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K).det
        rw [det_diag_units]; exact isUnit_one)]

theorem mat_dHom_e₁e₁ (α : Kˣ) : mat (dHom h α) ιe₁ ιe₁ = α := by
  rw [dHom_apply, mat_lev]
  rfl

theorem dHom_injective : Function.Injective (dHom h) := fun α β e => by
  apply Units.ext
  rw [← mat_dHom_e₁e₁ (h := h) α, ← mat_dHom_e₁e₁ (h := h) β, e]

theorem dHom_conj_uSU (α : Kˣ) (c : K) :
    dHom h α * uSU h c * (dHom h α)⁻¹ = uSU h ((α : K) ^ 2 * c) := by
  have hα : (α : K) ≠ 0 := α.ne_zero
  rw [dHom_apply, uSU, uSU, lev_inv, ← lev_mul, ← lev_mul]
  apply lev_congr
  have hinv : (!![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K)⁻¹ =
      !![((α⁻¹ : Kˣ) : K), 0; 0, (α : K)] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem exists_eq_uSU_mul_dHom {n : hypSU h 2 1} (hn : n ∈ N₁sub h)
    (hnU : n * uSU h 1 * n⁻¹ ∈ patSub h sI₁ isPattern_sI₁) :
    ∃ c : K, ∃ α : Kˣ, n = uSU h c * dHom h α := by
  have := h.charP
  obtain ⟨A, rfl⟩ := hn
  have hAu : IsUnit (A : Matrix (Fin 2) (Fin 2) K).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
  have hdet := A.det_coe
  rw [det_fin_two] at hdet
  set a := (A : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) K) 1 1
  have hc : c = 0 := by
    have hU := (U_entries (mem_patSub_sI₁.1 hnU).1).2.1
    rw [← lev_eq_leviSU A hAu, uSU, lev_inv, ← lev_mul, ← lev_mul, mat_lev] at hU
    change (((A : Matrix (Fin 2) (Fin 2) K) * !![1, 1; 0, 1] *
      (A : Matrix (Fin 2) (Fin 2) K)⁻¹ : Matrix (Fin 2) (Fin 2) K) 1 0) = 0 at hU
    rw [Matrix.inv_def, Matrix.SpecialLinearGroup.det_coe, Ring.inverse_one, one_smul,
      Matrix.adjugate_fin_two, Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) K)] at hU
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at hU
    have h2 : c * c = 0 := by
      linear_combination -hU
    exact mul_self_eq_zero.1 h2
  rw [hc, mul_zero, sub_zero] at hdet
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hd' : d = a⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hmat : (A : Matrix (Fin 2) (Fin 2) K) = !![1, a * b; 0, 1] *
      !![((Units.mk0 a ha : Kˣ) : K), 0; 0, (((Units.mk0 a ha)⁻¹ : Kˣ) : K)] := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, ← hd', ← upper_matrix hdet]
    rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) K)]
    change !![a, b; c, d] = _
    rw [hc]
  refine ⟨a * b, Units.mk0 a ha, ?_⟩
  rw [dHom_apply, uSU, ← lev_mul, ← lev_eq_leviSU A hAu]
  exact lev_congr hmat _ _

end Model

end CFSG.LocalAnalysis.EvenBN.U5
