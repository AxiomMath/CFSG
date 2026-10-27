module

public import CFSG.LieType.Steinberg.PartBRankOne

public section

namespace CFSG.SeitzReduction.E8Pilot

open Matrix CFSG.LieType.Steinberg

section SL2

variable {K : Type} [Field K]

theorem sl2Upper_add (a b : K) : sl2Upper (a + b) = sl2Upper a * sl2Upper b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, coe_sl2Upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2Lower_add (a b : K) : sl2Lower (a + b) = sl2Lower a * sl2Lower b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, coe_sl2Lower, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2Upper_zero : sl2Upper (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Upper]

theorem sl2Lower_zero : sl2Lower (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Lower]

theorem sl2Upper_injective : Function.Injective (sl2Upper : K → SpecialLinearGroup (Fin 2) K) := by
  intro a b h
  have := congrFun (congrFun (congrArg (fun M : SpecialLinearGroup (Fin 2) K =>
    (M : Matrix (Fin 2) (Fin 2) K)) h) 0) 1
  simpa [coe_sl2Upper] using this

theorem sl2Lower_injective : Function.Injective (sl2Lower : K → SpecialLinearGroup (Fin 2) K) := by
  intro a b h
  have := congrFun (congrFun (congrArg (fun M : SpecialLinearGroup (Fin 2) K =>
    (M : Matrix (Fin 2) (Fin 2) K)) h) 1) 0
  simpa [coe_sl2Lower] using this

variable [CharP K 2]

theorem eq_one_of_mul_self_eq_one_of_charTwo {p : K} (h : p * p = 1) : p = 1 := by
  have h2 : (p - 1) * (p - 1) = 0 := by
    have : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h - (p - 1) * this
  rcases mul_self_eq_zero.1 h2 with h3
  exact sub_eq_zero.1 h3

theorem eq_sl2Upper_of_commute {g : SpecialLinearGroup (Fin 2) K}
    (hg : g * sl2Upper 1 = sl2Upper 1 * g) :
    g = sl2Upper ((g : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  have hm := congrArg (fun M : SpecialLinearGroup (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K)) hg
  simp only [SpecialLinearGroup.coe_mul, coe_sl2Upper] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hdet := g.2
  rw [Matrix.det_fin_two, e00, mul_zero, sub_zero] at hdet
  have hd : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = (g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    linear_combination -e01
  rw [hd] at hdet
  have h1 := eq_one_of_mul_self_eq_one_of_charTwo hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Upper, h1, e00, hd]

theorem eq_sl2Lower_of_commute {g : SpecialLinearGroup (Fin 2) K}
    (hg : g * sl2Lower 1 = sl2Lower 1 * g) :
    g = sl2Lower ((g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hm := congrArg (fun M : SpecialLinearGroup (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K)) hg
  simp only [SpecialLinearGroup.coe_mul, coe_sl2Lower] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e10 := congrFun (congrFun hm 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  have hdet := g.2
  rw [Matrix.det_fin_two, e00, zero_mul, sub_zero] at hdet
  have hd : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = (g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    linear_combination e10
  rw [hd] at hdet
  have h1 := eq_one_of_mul_self_eq_one_of_charTwo hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Lower, h1, e00, hd]

omit [CharP K 2] in
@[expose] def sl2Diag (t : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

omit [CharP K 2] in
theorem coe_sl2Diag (t : Kˣ) :
    ((sl2Diag t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] :=
  rfl

omit [CharP K 2] in
@[expose] def sl2Weyl (a : K) : SpecialLinearGroup (Fin 2) K :=
  sl2Upper a * sl2Lower a⁻¹ * sl2Upper a

theorem coe_sl2Upper_mul_sl2Lower_mul_sl2Upper (u v : K) :
    ((sl2Upper u * sl2Lower v * sl2Upper u : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = !![1 + u * v, u * u * v; v, 1 + u * v] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination u * h2

theorem coe_sl2Weyl {a : K} (ha : a ≠ 0) :
    ((sl2Weyl a : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, a; a⁻¹, 0] := by
  rw [sl2Weyl, coe_sl2Upper_mul_sl2Lower_mul_sl2Upper, mul_inv_cancel₀ ha,
    show (1 : K) + 1 = 0 from CharTwo.add_self_eq_zero 1, mul_assoc, mul_inv_cancel₀ ha, mul_one]

theorem sl2Weyl_mul_sl2Weyl_one (t : Kˣ) : sl2Weyl (t : K) * sl2Weyl 1 = sl2Diag t := by
  ext i j
  rw [SpecialLinearGroup.coe_mul, coe_sl2Weyl t.ne_zero, coe_sl2Weyl one_ne_zero, coe_sl2Diag]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [CharP K 2] in
theorem sl2Diag_mul_sl2Upper_mul_inv (t : Kˣ) (b : K) :
    sl2Diag t * sl2Upper b * (sl2Diag t)⁻¹ = sl2Upper ((t : K) * t * b) := by
  rw [mul_inv_eq_iff_eq_mul]
  have ht := t.ne_zero
  ext i j
  simp only [SpecialLinearGroup.coe_mul, coe_sl2Diag, coe_sl2Upper]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
  field_simp

omit [CharP K 2] in
theorem sl2Weyl_mul_sl2Diag_mul_inv [CharP K 2] {a : K} (ha : a ≠ 0) (t : Kˣ) :
    sl2Weyl a * sl2Diag t * (sl2Weyl a)⁻¹ = sl2Diag t⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  have ht := t.ne_zero
  ext i j
  simp only [SpecialLinearGroup.coe_mul, coe_sl2Diag, coe_sl2Weyl ha]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
  all_goals ring

omit [CharP K 2] in
theorem sl2Diag_inv (t : Kˣ) : sl2Diag t⁻¹ = (sl2Diag t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  have ht := t.ne_zero
  ext i j
  simp only [SpecialLinearGroup.coe_mul, coe_sl2Diag, SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, ht]

variable [Finite K]

theorem exists_ringEquiv_of_forall_sl2 {k : Type} [Field k] (ι : k →+* K)
    (hk : ∃ c : k, c ≠ 0 ∧ c ≠ 1) (β : MulAut (SpecialLinearGroup (Fin 2) K))
    (hx : ∀ c : k, β (sl2Upper (ι c)) = sl2Upper (ι c))
    (hy : ∀ c : k, β (sl2Lower (ι c)) = sl2Lower (ι c)) :
    ∃ ρ : K ≃+* K, (∀ c, ρ (ι c) = ι c) ∧
      ∀ a : K, β (sl2Upper a) = sl2Upper (ρ a) ∧ β (sl2Lower a) = sl2Lower (ρ a) := by
  have hx1 : β (sl2Upper 1) = sl2Upper 1 := by simpa using hx 1
  have hy1 : β (sl2Lower 1) = sl2Lower 1 := by simpa using hy 1
  set f : K → K := fun a =>
    ((β (sl2Upper a) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 with hfdef
  set g : K → K := fun a =>
    ((β (sl2Lower a) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 with hgdef
  have hf : ∀ a, β (sl2Upper a) = sl2Upper (f a) := by
    intro a
    apply eq_sl2Upper_of_commute
    rw [← hx1, ← map_mul, ← map_mul, ← sl2Upper_add, ← sl2Upper_add, add_comm]
  have hg : ∀ a, β (sl2Lower a) = sl2Lower (g a) := by
    intro a
    apply eq_sl2Lower_of_commute
    rw [← hy1, ← map_mul, ← map_mul, ← sl2Lower_add, ← sl2Lower_add, add_comm]
  have hfadd : ∀ a b, f (a + b) = f a + f b := fun a b => sl2Upper_injective (by
    rw [← hf, sl2Upper_add, map_mul, hf, hf, ← sl2Upper_add])
  have hf0 : f 0 = 0 := sl2Upper_injective (by rw [← hf, sl2Upper_zero, map_one])
  have hg0 : g 0 = 0 := sl2Lower_injective (by rw [← hg, sl2Lower_zero, map_one])
  have hfι : ∀ c, f (ι c) = ι c := fun c => sl2Upper_injective (by rw [← hf, hx])
  have hf1 : f 1 = 1 := by simpa using hfι 1
  have hfinj : Function.Injective f := fun a b h =>
    sl2Upper_injective (β.injective (by rw [hf, hf, h]))
  obtain ⟨c₀, hc₀, hc₁⟩ := hk
  set t : Kˣ := Units.mk0 (ι c₀) (by rwa [ne_eq, map_eq_zero_iff ι ι.injective]) with ht
  have hW1 : β (sl2Weyl 1) = sl2Weyl 1 := by
    rw [sl2Weyl, map_mul, map_mul, hx1, inv_one, hy1]
  have hWt : β (sl2Weyl (t : K)) = sl2Weyl (t : K) := by
    rw [sl2Weyl, map_mul, map_mul, ht, Units.val_mk0, hx c₀, ← map_inv₀, hy]
  have hD : β (sl2Diag t) = sl2Diag t := by rw [← sl2Weyl_mul_sl2Weyl_one, map_mul, hWt, hW1]
  have hDinv : β (sl2Diag t⁻¹) = sl2Diag t⁻¹ := by rw [sl2Diag_inv, map_inv, hD]
  have htt : (t : K) ≠ (t : K)⁻¹ := by
    intro h
    have h1 : (t : K) * t = 1 := by
      calc (t : K) * t = (t : K) * (t : K)⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ t.ne_zero
    have h2 := eq_one_of_mul_self_eq_one_of_charTwo h1
    rw [ht, Units.val_mk0, ← map_one ι] at h2
    exact hc₁ (ι.injective h2)
  have hkey : ∀ a : K, a ≠ 0 → f a * g a⁻¹ = 1 := by
    intro a ha
    have h1 := congrArg β (sl2Weyl_mul_sl2Diag_mul_inv ha t)
    rw [map_mul, map_mul, map_inv, hD, hDinv, sl2Weyl, map_mul, map_mul, hf, hg] at h1
    have h2 : sl2Upper (f a) * sl2Lower (g a⁻¹) * sl2Upper (f a) * sl2Diag t =
        sl2Diag t⁻¹ * (sl2Upper (f a) * sl2Lower (g a⁻¹) * sl2Upper (f a)) := by
      rw [← h1]; group
    have h3 := congrFun (congrFun (congrArg (fun X : SpecialLinearGroup (Fin 2) K =>
      (X : Matrix (Fin 2) (Fin 2) K)) h2) 0) 0
    simp [SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, coe_sl2Diag, Matrix.mul_apply,
      Fin.sum_univ_two, Units.val_inv_eq_inv_val] at h3
    have h4 : (1 + f a * g a⁻¹) * ((t : K) - (t : K)⁻¹) = 0 := by
      linear_combination h3
    rcases mul_eq_zero.1 h4 with h5 | h5
    · have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h5 - h2'
    · exact absurd (sub_eq_zero.1 h5) htt
  have hgf : ∀ a : K, a ≠ 0 → g a⁻¹ = (f a)⁻¹ := fun a ha => eq_inv_of_mul_eq_one_right (hkey a ha)
  have hfne : ∀ a : K, a ≠ 0 → f a ≠ 0 := fun a ha h => ha (hfinj (by rw [h, hf0]))
  have hDf : ∀ s : Kˣ, β (sl2Diag s) = sl2Diag (Units.mk0 (f s) (hfne s s.ne_zero)) := by
    intro s
    have hWs : β (sl2Weyl (s : K)) = sl2Weyl (f s) := by
      rw [sl2Weyl, map_mul, map_mul, hf, hg, hgf s s.ne_zero, sl2Weyl]
    rw [← sl2Weyl_mul_sl2Weyl_one, map_mul, hWs, hW1, ← sl2Weyl_mul_sl2Weyl_one, Units.val_mk0]
  have hfsq : ∀ a b : K, a ≠ 0 → f (a * a * b) = f a * f a * f b := by
    intro a b ha
    have h1 := congrArg β (sl2Diag_mul_sl2Upper_mul_inv (Units.mk0 a ha) b)
    rw [map_mul, map_mul, map_inv, hDf, hf, hf, sl2Diag_mul_sl2Upper_mul_inv, Units.val_mk0,
      Units.val_mk0] at h1
    exact (sl2Upper_injective h1).symm
  have hfmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    by_cases ha : a = 0
    · rw [ha, zero_mul, hf0, zero_mul]
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact ha (by rw [hr, mul_zero])
    have h1 := hfsq r b hr0
    have h2 := hfsq r 1 hr0
    rw [mul_one, hf1, mul_one] at h2
    rw [hr, h1, h2]
  let ρh : K →+* K :=
    { toFun := f, map_one' := hf1, map_mul' := hfmul, map_zero' := hf0, map_add' := hfadd }
  have hbij : Function.Bijective ρh := ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  refine ⟨RingEquiv.ofBijective ρh hbij, fun c => hfι c, fun a => ⟨hf a, ?_⟩⟩
  change β (sl2Lower a) = sl2Lower (f a)
  rw [hg]
  congr 1
  by_cases ha : a = 0
  · rw [ha, hg0, hf0]
  · have h1 := hgf a⁻¹ (inv_ne_zero ha)
    rw [inv_inv] at h1
    rw [h1]
    have h2 : f a * f a⁻¹ = 1 := by rw [← hfmul, mul_inv_cancel₀ ha, hf1]
    exact inv_eq_of_mul_eq_one_left h2

end SL2

end CFSG.SeitzReduction.E8Pilot
