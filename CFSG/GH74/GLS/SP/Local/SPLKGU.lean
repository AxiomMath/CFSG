module

public import CFSG.GH74.GLS.IVK.L2.TorusMatrices
public import CFSG.GH74.GLS.Stage4.HexCD4Weyl

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup
open CFSG.GH74.GLS.Stage4.Hex
open CFSG.GH74.GLS.IVK.L2Torus (inv_apply_00 inv_apply_01 inv_apply_10 inv_apply_11 sl2_det)

section KGU

variable {F : Type} [Field F]

theorem conj_sl2U_form {g : SL2 F} {μ : F} (h : g * sl2U 1 * g⁻¹ = sl2U μ) :
    (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = μ := by
  have hdet := sl2_det g
  have h00 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have h01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have h10 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp only [CFSG.GH74.GLS.IVK.L2Torus.mul_apply', inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, coe_sl2U] at h00 h01 h10
  simp at h00 h01 h10
  have hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 = 0 := by linear_combination -h10
  refine ⟨pow_eq_zero_iff (by norm_num) |>.mp hc, ?_⟩
  linear_combination h01


theorem sl2D_conj_sl2U (t : Fˣ) (s : F) : sl2D t * sl2U s * (sl2D t)⁻¹ = sl2U ((t : F) ^ 2 * s) := by
  rw [mul_inv_eq_iff_eq_mul, sl2D_mul_sl2U_eq]

theorem sl2W_eq_prod : sl2W F = sl2U 1 * sl2L (-1) * sl2U 1 := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]


theorem antidiag_of_swap {m : SL2 F} {μ : Fˣ} (hμ : (μ : F) ^ 2 ≠ 1)
    (h : m * sl2D μ = sl2D μ⁻¹ * m) :
    (m : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  have hne : (μ : F) - (μ : F)⁻¹ ≠ 0 := by
    intro h0
    apply hμ
    have h1 : (μ : F) = (μ : F)⁻¹ := sub_eq_zero.mp h0
    calc (μ : F) ^ 2 = (μ : F) * (μ : F)⁻¹ := by rw [sq]; nth_rewrite 2 [h1]; rfl
      _ = 1 := mul_inv_cancel₀ hμ0
  have h00 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have h11 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Units.val_inv_eq_inv_val] at h00 h11
  constructor
  · have : (m : Matrix (Fin 2) (Fin 2) F) 0 0 * ((μ : F) - (μ : F)⁻¹) = 0 := by
      linear_combination h00
    exact (mul_eq_zero.mp this).resolve_right hne
  · have : (m : Matrix (Fin 2) (Fin 2) F) 1 1 * ((μ : F) - (μ : F)⁻¹) = 0 := by
      linear_combination -h11
    exact (mul_eq_zero.mp this).resolve_right hne


theorem weyl_rigid {m : SL2 F} (h00 : (m : Matrix (Fin 2) (Fin 2) F) 0 0 = 0)
    (h11 : (m : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (h : m = sl2U 1 * (m * sl2U 1 * m⁻¹) * sl2U 1) : m = sl2W F := by
  have hdet := sl2_det m
  have e00 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have e01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have e10 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp only [CFSG.GH74.GLS.IVK.L2Torus.mul_apply', inv_apply_00, inv_apply_01, inv_apply_10,
    inv_apply_11, coe_sl2U] at e00 e01 e10
  simp [h00, h11] at hdet e00 e01 e10
  set r := (m : Matrix (Fin 2) (Fin 2) F) 0 1 with hr
  set s := (m : Matrix (Fin 2) (Fin 2) F) 1 0 with hs
  have hs2 : s ^ 2 = 1 := by linear_combination e00 + hdet
  have hs1 : s = -1 := by linear_combination e10 - hs2
  have hr1 : r = 1 := by rw [hs1] at hdet; linear_combination hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, hr1, hs1, ← hr, ← hs]


theorem sl2U_inv' (s : F) : (sl2U s)⁻¹ = sl2U (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← sl2U_add, add_neg_cancel, sl2U_zero])

theorem sl2D_inv' (t : Fˣ) : (sl2D t)⁻¹ = sl2D t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_aut_fixing_U [Finite F] (h5 : 5 ≤ Nat.card F)
    (α : SL2 F ≃* SL2 F) (hα : ∀ s : F, α (sl2U s) = sl2U s) :
    ∃ x : F, ∀ g : SL2 F, α g = sl2U x * g * (sl2U x)⁻¹ := by
  classical
  obtain ⟨lam, hlam⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf lam = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hlam, Nat.card_units]
  have hlam2 : (lam : F) ^ 2 ≠ 1 := by
    intro h
    have h' : lam ^ 2 = 1 := Units.ext (by simpa using h)
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hord] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  set g : SL2 F := α (sl2D lam) with hg
  have hconj : g * sl2U 1 * g⁻¹ = sl2U ((lam : F) ^ 2) := by
    have := congrArg α (sl2D_conj_sl2U lam 1)
    rw [map_mul, map_mul, map_inv, hα, hα, mul_one] at this
    exact this
  obtain ⟨hc, ha⟩ := conj_sl2U_form hconj
  have hdet := sl2_det g
  rw [hc, mul_zero, sub_zero] at hdet
  set a : F := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with hadef
  set b : F := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hbdef
  set e : F := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hedef
  have hae : a * e = 1 := hdet
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one hae
  have hne : a - e ≠ 0 := by
    intro h0
    have h1 : a = e := sub_eq_zero.mp h0
    apply hlam2
    rw [← ha, sq, ← hae]
    nth_rewrite 2 [h1]
    rfl
  set x : F := -b / (a - e) with hx
  have hxb : b + x * (a - e) = 0 := by rw [hx]; field_simp; ring
  let β : SL2 F →* SL2 F := (MulAut.conj (sl2U x)⁻¹).toMonoidHom.comp α.toMonoidHom
  have hβapp : ∀ y : SL2 F, β y = sl2U (-x) * α y * sl2U x := fun y => by
    show (sl2U x)⁻¹ * α y * ((sl2U x)⁻¹)⁻¹ = _
    rw [sl2U_inv', sl2U_inv', neg_neg]
  have hβu : ∀ s : F, β (sl2U s) = sl2U s := fun s => by
    rw [hβapp, hα, ← sl2U_add, ← sl2U_add]; congr 1; ring
  have hβd : β (sl2D lam) = sl2D (Units.mk0 a ha0) := by
    rw [hβapp, ← hg]
    apply sl2_ext
    ext i j
    fin_cases i <;> fin_cases j <;>
    · simp only [CFSG.GH74.GLS.IVK.L2Torus.mul_apply'] at *
      simp [hc, ← hadef, ← hbdef, ← hedef]
      all_goals first
        | linear_combination hxb
        | exact eq_inv_of_mul_eq_one_right hae
  have hμ2 : ((Units.mk0 a ha0 : Fˣ) : F) ^ 2 ≠ 1 := by simpa [ha] using hlam2
  have hswap : β (sl2W F) * sl2D (Units.mk0 a ha0) =
      sl2D (Units.mk0 a ha0)⁻¹ * β (sl2W F) := by
    have h1 := congrArg β (sl2W_mul_sl2D lam)
    rw [map_mul, map_mul] at h1
    have h2 : β (sl2D lam⁻¹) = sl2D (Units.mk0 a ha0)⁻¹ := by
      rw [← sl2D_inv', map_inv, hβd, sl2D_inv']
    rw [hβd, h2] at h1
    exact h1
  obtain ⟨hm00, hm11⟩ := antidiag_of_swap hμ2 hswap
  have hL : sl2L (-1) = sl2W F * sl2U 1 * (sl2W F)⁻¹ :=
    eq_mul_inv_of_mul_eq (sl2W_mul_sl2U (1 : F)).symm
  have hrel : β (sl2W F) = sl2U 1 * (β (sl2W F) * sl2U 1 * (β (sl2W F))⁻¹) * sl2U 1 := by
    calc β (sl2W F) = β (sl2U 1 * sl2L (-1) * sl2U 1) := by rw [← sl2W_eq_prod]
      _ = sl2U 1 * (β (sl2W F) * sl2U 1 * (β (sl2W F))⁻¹) * sl2U 1 := by
        rw [map_mul, map_mul, hL, map_mul, map_mul, map_inv, hβu]
  have hW : β (sl2W F) = sl2W F := weyl_rigid hm00 hm11 hrel
  have hβL : ∀ c : F, β (sl2L c) = sl2L c := by
    intro c
    have h1 : sl2L c = sl2W F * sl2U (-c) * (sl2W F)⁻¹ := by
      have := sl2W_mul_sl2U (-c)
      rw [neg_neg] at this
      exact eq_mul_inv_of_mul_eq this.symm
    rw [h1, map_mul, map_mul, map_inv, hW, hβu]
  have hid : ∀ y : SL2 F, β y = y := by
    intro y
    have hmem := sl2_mem_closure y
    have hle : Subgroup.closure (Set.range (sl2U (F := F)) ∪ Set.range (sl2L (F := F))) ≤
        MonoidHom.eqLocus β (MonoidHom.id _) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hβu c
      · exact hβL c
    exact hle hmem
  refine ⟨x, fun y => ?_⟩
  have h1 := hid y
  have e : sl2U (-x) = (sl2U x)⁻¹ := (sl2U_inv' x).symm
  rw [hβapp, e] at h1
  calc α y = sl2U x * ((sl2U x)⁻¹ * α y * sl2U x) * (sl2U x)⁻¹ := by group
    _ = sl2U x * y * (sl2U x)⁻¹ := by rw [h1]

end KGU

end CFSG.GH74.GLS.SP.Local
