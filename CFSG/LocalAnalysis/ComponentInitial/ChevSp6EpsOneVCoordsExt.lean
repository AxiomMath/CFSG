module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneModuleDataCheck
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.ExtOne

open Matrix

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

def enc (B : M₃) : ℕ :=
  (B 0 0).val + 2 * (B 0 1).val + 4 * (B 0 2).val + 8 * (B 1 0).val + 16 * (B 1 1).val +
  32 * (B 1 2).val + 64 * (B 2 0).val + 128 * (B 2 1).val + 256 * (B 2 2).val

def dec (n : ℕ) : M₃ := Matrix.of fun i j => ((nb n (3 * i.val + j.val) : ℕ) : ZMod 2)

theorem nb_sum {v0 v1 v2 v3 v4 v5 v6 v7 v8 : ℕ} (h0 : v0 < 2) (h1 : v1 < 2) (h2 : v2 < 2)
    (h3 : v3 < 2) (h4 : v4 < 2) (h5 : v5 < 2) (h6 : v6 < 2) (h7 : v7 < 2) (h8 : v8 < 2) :
    let n := v0 + 2 * v1 + 4 * v2 + 8 * v3 + 16 * v4 + 32 * v5 + 64 * v6 + 128 * v7 + 256 * v8
    nb n 0 = v0 ∧ nb n 1 = v1 ∧ nb n 2 = v2 ∧ nb n 3 = v3 ∧ nb n 4 = v4 ∧ nb n 5 = v5 ∧
      nb n 6 = v6 ∧ nb n 7 = v7 ∧ nb n 8 = v8 := by
  intro n
  simp only [n, nb, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem nb_enc (B : M₃) :
    nb (enc B) 0 = (B 0 0).val ∧ nb (enc B) 1 = (B 0 1).val ∧ nb (enc B) 2 = (B 0 2).val ∧
      nb (enc B) 3 = (B 1 0).val ∧ nb (enc B) 4 = (B 1 1).val ∧ nb (enc B) 5 = (B 1 2).val ∧
      nb (enc B) 6 = (B 2 0).val ∧ nb (enc B) 7 = (B 2 1).val ∧ nb (enc B) 8 = (B 2 2).val :=
  nb_sum (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)

theorem val_dot3 : ∀ a b c d e f : ZMod 2,
    (a * d + b * e + c * f).val = dot3 a.val b.val c.val d.val e.val f.val := by
  decide

theorem val_add2 : ∀ a b : ZMod 2, (a + b).val = (a.val + b.val) % 2 := by
  decide

theorem enc_mul (X Y : M₃) : enc (X * Y) = mul9 (enc X) (enc Y) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := nb_enc X
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8⟩ := nb_enc Y
  rw [mul9, x0, x1, x2, x3, x4, x5, x6, x7, x8, y0, y1, y2, y3, y4, y5, y6, y7, y8]
  simp only [enc, mul_apply, Fin.sum_univ_three, val_dot3]

theorem enc_add (X Y : M₃) : enc (X + Y) = add9 (enc X) (enc Y) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := nb_enc X
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8⟩ := nb_enc Y
  rw [add9, x0, x1, x2, x3, x4, x5, x6, x7, x8, y0, y1, y2, y3, y4, y5, y6, y7, y8]
  simp only [enc, Matrix.add_apply, val_add2]

theorem enc_inj {X Y : M₃} (h : enc X = enc Y) : X = Y := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := nb_enc X
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8⟩ := nb_enc Y
  rw [h] at x0 x1 x2 x3 x4 x5 x6 x7 x8
  ext i j
  apply ZMod.val_injective
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega

theorem nb_lt (n k : ℕ) : nb n k < 2 := Nat.mod_lt _ (by norm_num)

theorem enc_dec {n : ℕ} (hn : n < 512) : enc (dec n) = n := by
  have hv : ∀ k, (((nb n k : ℕ) : ZMod 2)).val = nb n k := fun k => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (nb_lt n k)]
  simp only [enc, dec, of_apply, Fin.val_zero, Fin.val_one, Fin.val_two, hv]
  simp only [nb]
  omega

theorem enc_lt (B : M₃) : enc B < 512 := by
  have := ZMod.val_lt (B 0 0); have := ZMod.val_lt (B 0 1); have := ZMod.val_lt (B 0 2)
  have := ZMod.val_lt (B 1 0); have := ZMod.val_lt (B 1 1); have := ZMod.val_lt (B 1 2)
  have := ZMod.val_lt (B 2 0); have := ZMod.val_lt (B 2 1); have := ZMod.val_lt (B 2 2)
  unfold enc
  omega

def pmul (p q : M₃ × M₃) : M₃ × M₃ := (p.1 * q.1, p.1 * q.2 + p.2 * q.1)

def ppow (p : M₃ × M₃) : ℕ → M₃ × M₃
  | 0 => (1, 0)
  | n + 1 => pmul (ppow p n) p

def encP (p : M₃ × M₃) : ℕ × ℕ := (enc p.1, enc p.2)

theorem encP_pmul (p q : M₃ × M₃) : encP (pmul p q) = pmulN (encP p) (encP q) := by
  simp only [encP, pmul, pmulN, enc_mul, enc_add]

theorem enc_one : enc 1 = oneN := by decide

theorem enc_zero : enc 0 = 0 := by decide

theorem encP_one : encP ((1 : M₃), (0 : M₃)) = (oneN, 0) := by
  simp only [encP, enc_one, enc_zero]

theorem encP_ppow (p : M₃ × M₃) (n : ℕ) : encP (ppow p n) = ppowN (encP p) n := by
  induction n with
  | zero => exact encP_one
  | succ n ih => rw [ppow, ppowN, encP_pmul, ih]

def extA : M₃ := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

def extB : M₃ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem enc_extA : enc extA = aN := by decide

theorem enc_extB : enc extB = bN := by decide

theorem ext_spec {x y : ℕ} (hx : x < 512) (hy : y < 512)
    (hA : extRelA x = true) (hB : extRelB y = true) (hAB : extRelAB x y = true) :
    ∃ m < 512, extCob x y m = true := by
  have h := ext_check
  unfold extCheck at h
  rw [List.all_eq_true] at h
  have h1 := h x (List.mem_range.2 hx)
  simp only [hA, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 y (List.mem_range.2 hy)
  simp only [hB, hAB, Bool.not_true, Bool.false_or, List.any_eq_true] at h2
  obtain ⟨m, hm, hm'⟩ := h2
  exact ⟨m, List.mem_range.1 hm, hm'⟩

theorem ext_matrix {X Y : M₃}
    (hA : pmul (extA, X) (extA, X) = (1, 0)) (hB : ppow (extB, Y) 3 = (1, 0))
    (hAB : ppow (pmul (extA, X) (extB, Y)) 7 = (1, 0)) :
    ∃ m : M₃, X = extA * m + m * extA ∧ Y = extB * m + m * extB := by
  have hA' : extRelA (enc X) = true := by
    have e := congrArg encP hA
    rw [encP_pmul, encP_one] at e
    simp only [encP, enc_extA] at e
    simp only [extRelA, e, beq_self_eq_true]
  have hB' : extRelB (enc Y) = true := by
    have e := congrArg encP hB
    rw [encP_ppow, encP_one] at e
    simp only [encP, enc_extB] at e
    simp only [extRelB, e, beq_self_eq_true]
  have hAB' : extRelAB (enc X) (enc Y) = true := by
    have e := congrArg encP hAB
    rw [encP_ppow, encP_pmul, encP_one] at e
    simp only [encP, enc_extA, enc_extB] at e
    simp only [extRelAB, e, beq_self_eq_true]
  obtain ⟨m, hm, hcob⟩ := ext_spec (enc_lt X) (enc_lt Y) hA' hB' hAB'
  simp only [extCob, Bool.and_eq_true, beq_iff_eq] at hcob
  refine ⟨dec m, enc_inj ?_, enc_inj ?_⟩
  · rw [enc_add, enc_mul, enc_mul, enc_extA, enc_dec hm]
    exact hcob.1
  · rw [enc_add, enc_mul, enc_mul, enc_extB, enc_dec hm]
    exact hcob.2

theorem extA_mul_self : extA * extA = 1 := by decide

theorem extB_cube : extB * (extB * extB) = 1 := by decide

theorem extB_cube' : extB * extB * extB = 1 := by decide

def gA : GL (Fin 3) (ZMod 2) := ⟨extA, extA, extA_mul_self, extA_mul_self⟩

def gB : GL (Fin 3) (ZMod 2) := ⟨extB, extB * extB, extB_cube, extB_cube'⟩

theorem gA_sq : gA * gA = 1 := Units.ext extA_mul_self

theorem gB_cube : gB ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; decide)

theorem gAB_seven : (gA * gB) ^ 7 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; decide)

theorem orderOf_gB : orderOf gB = 3 :=
  orderOf_eq_prime gB_cube fun h => absurd (congrArg Units.val h) (by decide)

theorem orderOf_gAB : orderOf (gA * gB) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime gAB_seven fun h => absurd (congrArg Units.val h) (by decide)

theorem orderOf_gC : orderOf (gA * gB * gB * gA * gB) = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1)
    (fun h => absurd (congrArg Units.val h) (by rw [Units.val_pow_eq_pow_val]; decide))
    (Units.ext (by rw [Units.val_pow_eq_pow_val]; decide))

theorem eq_top_of_mem {H : Subgroup (GL (Fin 3) (ZMod 2))} (ha : gA ∈ H) (hb : gB ∈ H) :
    H = ⊤ := by
  have h3 : 3 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hb
    rwa [orderOf_gB] at this
  have h7 : 7 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H (mul_mem ha hb)
    rwa [orderOf_gAB] at this
  have h4 : 4 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H (mul_mem (mul_mem (mul_mem (mul_mem ha hb) hb) ha) hb)
    rwa [orderOf_gC] at this
  have hcard := BinarySymplecticSix.FusionOrbits.card_GL_three_two
  have h168 : Nat.card H ∣ 168 := hcard ▸ Subgroup.card_subgroup_dvd_card H
  have hle := Nat.le_of_dvd (by norm_num) h168
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hH : Nat.card H = 84 ∨ Nat.card H = 168 := by omega
  rcases hH with hH | hH
  · exfalso
    have hidx : H.index = 2 := by
      have := H.index_mul_card
      rw [hH, hcard] at this
      omega
    have := Subgroup.normal_of_index_eq_two hidx
    have := BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · rw [h, Subgroup.card_bot] at hH
      omega
    · rw [h, Subgroup.card_top, hcard] at hH
      omega
  · exact (Subgroup.card_eq_iff_eq_top H).1 (by rw [hH, hcard])

theorem m3_add_self (X : M₃) : X + X = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (X i j)

theorem m3_eq_of_zero_eq_add {X Y : M₃} (h : 0 = X + Y) : X = Y := by
  calc X = X + (Y + Y) := by rw [m3_add_self, add_zero]
    _ = (X + Y) + Y := by rw [add_assoc]
    _ = Y := by rw [← h, zero_add]

def cobSub (C : GL (Fin 3) (ZMod 2) → M₃)
    (hC : ∀ g h, C (g * h) = (g : M₃) * C h + C g * (h : M₃)) (m : M₃) :
    Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {g | C g = (g : M₃) * m + m * (g : M₃)}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [hC, hg, hh, Units.val_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [add_assoc, ← add_assoc ((g : M₃) * (m * (h : M₃))), m3_add_self, zero_add]
  one_mem' := by
    have e := hC 1 1
    rw [mul_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at e
    simp only [Set.mem_ofPred_eq, Units.val_one, Matrix.one_mul, Matrix.mul_one, m3_add_self]
    exact left_eq_add.1 e
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h1 : C 1 = 0 := by
      have e := hC 1 1
      rw [mul_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at e
      exact left_eq_add.1 e
    have e := hC g g⁻¹
    rw [mul_inv_cancel, h1] at e
    have e2 := m3_eq_of_zero_eq_add e
    have e3 : C g⁻¹ = ((g⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) * ((g : M₃) * C g⁻¹) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [e3, e2, hg]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Units.mul_inv,
      Units.inv_mul_cancel_left, Matrix.mul_one]
    rw [add_comm]

theorem exists_coboundary (C : GL (Fin 3) (ZMod 2) → M₃)
    (hC : ∀ g h, C (g * h) = (g : M₃) * C h + C g * (h : M₃)) :
    ∃ m : M₃, ∀ g, C g = (g : M₃) * m + m * (g : M₃) := by
  have hC1 : C 1 = 0 := by
    have e := hC 1 1
    rw [mul_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at e
    exact left_eq_add.1 e
  have hφ : ∀ g h : GL (Fin 3) (ZMod 2), pmul ((g : M₃), C g) ((h : M₃), C h) =
      (((g * h : GL (Fin 3) (ZMod 2)) : M₃), C (g * h)) := by
    intro g h
    simp only [pmul, Units.val_mul, hC]
  have hpow : ∀ (g : GL (Fin 3) (ZMod 2)) (n : ℕ),
      ppow ((g : M₃), C g) n = (((g ^ n : GL (Fin 3) (ZMod 2)) : M₃), C (g ^ n)) := by
    intro g n
    induction n with
    | zero => simp only [ppow, pow_zero, Units.val_one, hC1]
    | succ n ih => rw [ppow, ih, hφ, pow_succ]
  have hA : pmul (extA, C gA) (extA, C gA) = (1, 0) := by
    have e := hφ gA gA
    rw [gA_sq, Units.val_one, hC1] at e
    exact e
  have hB : ppow (extB, C gB) 3 = (1, 0) := by
    have e := hpow gB 3
    rw [gB_cube, Units.val_one, hC1] at e
    exact e
  have hAB : ppow (pmul (extA, C gA) (extB, C gB)) 7 = (1, 0) := by
    have e := hpow (gA * gB) 7
    rw [gAB_seven, Units.val_one, hC1, ← hφ] at e
    exact e
  obtain ⟨m, hma, hmb⟩ := ext_matrix hA hB hAB
  have htop := eq_top_of_mem (H := cobSub C hC m) hma hmb
  exact ⟨m, fun g => (htop ▸ Subgroup.mem_top g : g ∈ cobSub C hC m)⟩

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.ExtOne
