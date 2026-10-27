module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33Check

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

abbrev S3 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)

@[expose] def rn (x : S3) : Nat :=
  (x.1 0 0).val + 3 * (x.1 0 1).val + 9 * (x.1 0 2).val + 27 * (x.1 1 0).val +
    81 * (x.1 1 1).val + 243 * (x.1 1 2).val + 729 * (x.1 2 0).val + 2187 * (x.1 2 1).val +
    6561 * (x.1 2 2).val

theorem val_dot3 (a b c d e f : ZMod 3) :
    (a * d + b * e + c * f).val = (a.val * d.val + b.val * e.val + c.val * f.val) % 3 := by
  revert a b c d e f
  decide +kernel

theorem val_det (m0 m1 m2 m3 m4 m5 m6 m7 m8 : ZMod 3) :
    (m0 * m4 * m8 - m0 * m5 * m7 - m1 * m3 * m8 + m1 * m5 * m6 + m2 * m3 * m7 - m2 * m4 * m6).val =
      (m0.val * m4.val * m8.val + 2 * (m0.val * m5.val * m7.val) +
        2 * (m1.val * m3.val * m8.val) + m1.val * m5.val * m6.val + m2.val * m3.val * m7.val +
        2 * (m2.val * m4.val * m6.val)) % 3 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h : (((m0.val * m4.val * m8.val + 2 * (m0.val * m5.val * m7.val) +
        2 * (m1.val * m3.val * m8.val) + m1.val * m5.val * m6.val + m2.val * m3.val * m7.val +
        2 * (m2.val * m4.val * m6.val) : ℕ)) : ZMod 3) =
      m0 * m4 * m8 - m0 * m5 * m7 - m1 * m3 * m8 + m1 * m5 * m6 + m2 * m3 * m7 - m2 * m4 * m6 := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination (m0 * m5 * m7 + m1 * m3 * m8 + m2 * m4 * m6) * h3
  rw [← h, ZMod.val_natCast]

theorem dg_rn (x : S3) (i j : Fin 3) : dg (rn x) (3 * i.val + j.val) = (x.1 i j).val := by
  have h : ∀ a b : Fin 3, (x.1 a b).val < 3 := fun a b => ZMod.val_lt _
  have h00 := h 0 0
  have h01 := h 0 1
  have h02 := h 0 2
  have h10 := h 1 0
  have h11 := h 1 1
  have h12 := h 1 2
  have h20 := h 2 0
  have h21 := h 2 1
  have h22 := h 2 2
  fin_cases i <;> fin_cases j <;> simp only [dg, rn] <;> norm_num <;> omega

theorem rn_lt (x : S3) : rn x < 19683 := by
  have h : ∀ a b : Fin 3, (x.1 a b).val < 3 := fun a b => ZMod.val_lt _
  have h00 := h 0 0
  have h01 := h 0 1
  have h02 := h 0 2
  have h10 := h 1 0
  have h11 := h 1 1
  have h12 := h 1 2
  have h20 := h 2 0
  have h21 := h 2 1
  have h22 := h 2 2
  unfold rn
  omega

theorem rn_mul (x y : S3) : rn (x * y) = nmul (rn x) (rn y) := by
  have d00 : dg (rn x) 0 = (x.1 0 0).val := dg_rn x 0 0
  have d01 : dg (rn x) 1 = (x.1 0 1).val := dg_rn x 0 1
  have d02 : dg (rn x) 2 = (x.1 0 2).val := dg_rn x 0 2
  have d10 : dg (rn x) 3 = (x.1 1 0).val := dg_rn x 1 0
  have d11 : dg (rn x) 4 = (x.1 1 1).val := dg_rn x 1 1
  have d12 : dg (rn x) 5 = (x.1 1 2).val := dg_rn x 1 2
  have d20 : dg (rn x) 6 = (x.1 2 0).val := dg_rn x 2 0
  have d21 : dg (rn x) 7 = (x.1 2 1).val := dg_rn x 2 1
  have d22 : dg (rn x) 8 = (x.1 2 2).val := dg_rn x 2 2
  have e00 : dg (rn y) 0 = (y.1 0 0).val := dg_rn y 0 0
  have e01 : dg (rn y) 1 = (y.1 0 1).val := dg_rn y 0 1
  have e02 : dg (rn y) 2 = (y.1 0 2).val := dg_rn y 0 2
  have e10 : dg (rn y) 3 = (y.1 1 0).val := dg_rn y 1 0
  have e11 : dg (rn y) 4 = (y.1 1 1).val := dg_rn y 1 1
  have e12 : dg (rn y) 5 = (y.1 1 2).val := dg_rn y 1 2
  have e20 : dg (rn y) 6 = (y.1 2 0).val := dg_rn y 2 0
  have e21 : dg (rn y) 7 = (y.1 2 1).val := dg_rn y 2 1
  have e22 : dg (rn y) 8 = (y.1 2 2).val := dg_rn y 2 2
  simp only [nmul, d00, d01, d02, d10, d11, d12, d20, d21, d22, e00, e01, e02, e10, e11, e12, e20,
    e21, e22]
  simp only [rn, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, val_dot3]

theorem rn_inj : Function.Injective rn := by
  intro x y h
  have key : ∀ i j : Fin 3, (x.1 i j).val = (y.1 i j).val := by
    intro i j
    rw [← dg_rn x i j, ← dg_rn y i j, h]
  apply Subtype.ext
  ext i j
  exact ZMod.val_injective 3 (key i j)

theorem rn_one : rn (1 : S3) = nid := by
  simp [rn, nid]
  decide

theorem ndet_rn (x : S3) : ndet (rn x) = 1 := by
  have d00 : dg (rn x) 0 = (x.1 0 0).val := dg_rn x 0 0
  have d01 : dg (rn x) 1 = (x.1 0 1).val := dg_rn x 0 1
  have d02 : dg (rn x) 2 = (x.1 0 2).val := dg_rn x 0 2
  have d10 : dg (rn x) 3 = (x.1 1 0).val := dg_rn x 1 0
  have d11 : dg (rn x) 4 = (x.1 1 1).val := dg_rn x 1 1
  have d12 : dg (rn x) 5 = (x.1 1 2).val := dg_rn x 1 2
  have d20 : dg (rn x) 6 = (x.1 2 0).val := dg_rn x 2 0
  have d21 : dg (rn x) 7 = (x.1 2 1).val := dg_rn x 2 1
  have d22 : dg (rn x) 8 = (x.1 2 2).val := dg_rn x 2 2
  simp only [ndet, d00, d01, d02, d10, d11, d12, d20, d21, d22]
  rw [← val_det]
  have hdet : x.1.det = 1 := x.2
  rw [Matrix.det_fin_three] at hdet
  rw [hdet]
  rfl

theorem rn_mem_nL (x : S3) : rn x ∈ nL := by
  unfold nL
  rw [List.mem_filter, List.mem_range]
  exact ⟨rn_lt x, by simpa using ndet_rn x⟩

@[expose] def mat (l : Nat) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![(dg l 0 : ZMod 3), (dg l 1 : ZMod 3), (dg l 2 : ZMod 3);
    (dg l 3 : ZMod 3), (dg l 4 : ZMod 3), (dg l 5 : ZMod 3);
    (dg l 6 : ZMod 3), (dg l 7 : ZMod 3), (dg l 8 : ZMod 3)]

theorem det_natCast (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Nat) :
    ((a0 : ZMod 3) * a4 * a8 - a0 * a5 * a7 - a1 * a3 * a8 + a1 * a5 * a6 + a2 * a3 * a7 -
      a2 * a4 * a6) =
      ((a0 * a4 * a8 + 2 * (a0 * a5 * a7) + 2 * (a1 * a3 * a8) + a1 * a5 * a6 + a2 * a3 * a7 +
        2 * (a2 * a4 * a6) : Nat) : ZMod 3) := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  push_cast
  linear_combination (-1 : ZMod 3) * ((a0 : ZMod 3) * a5 * a7 + a1 * a3 * a8 + a2 * a4 * a6) * h3

theorem det_mat (l : Nat) (h : ndet l = 1) : (mat l).det = 1 := by
  rw [Matrix.det_fin_three]
  simp only [mat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.tail_cons, Matrix.head_fin_const]
  rw [det_natCast]
  have h1 : (((ndet l : Nat)) : ZMod 3) = 1 := by rw [h]; rfl
  rw [← h1]
  unfold ndet
  rw [ZMod.natCast_mod]

@[expose] def ofN (l : Nat) (h : ndet l = 1) : S3 := ⟨mat l, det_mat l h⟩

theorem sum_dg (l : Nat) (hl : l < 19683) :
    dg l 0 + 3 * dg l 1 + 9 * dg l 2 + 27 * dg l 3 + 81 * dg l 4 + 243 * dg l 5 + 729 * dg l 6 +
      2187 * dg l 7 + 6561 * dg l 8 = l := by
  unfold dg
  norm_num
  omega

theorem dg_lt (l k : Nat) : dg l k < 3 := Nat.mod_lt _ (by norm_num)

theorem rn_ofN (l : Nat) (hl : l < 19683) (h : ndet l = 1) : rn (ofN l h) = l := by
  have hv : ∀ k : Nat, ((dg l k : Nat) : ZMod 3).val = dg l k := by
    intro k
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (dg_lt l k)
  have := sum_dg l hl
  simp only [rn, ofN, mat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.tail_cons, Matrix.head_fin_const, hv]
  exact this

theorem card_subtype_mem {l : List Nat} (h : l.Nodup) : Nat.card {a // a ∈ l} = l.length := by
  classical
  have e : {a // a ∈ l} ≃ ↥l.toFinset :=
    Equiv.subtypeEquivRight fun a => by simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h]

theorem mem_nL {a : Nat} : a ∈ nL ↔ a < 19683 ∧ ndet a = 1 := by
  unfold nL
  rw [List.mem_filter, List.mem_range]
  simp

theorem nL_nodup : nL.Nodup := (List.nodup_range).filter _

theorem nL_length : nL.length = 5616 := by
  decide +kernel

theorem card_S3 : Nat.card S3 = 5616 := by
  have e : S3 ≃ {a // a ∈ nL} :=
    { toFun := fun x => ⟨rn x, rn_mem_nL x⟩
      invFun := fun a => ofN a.1 (mem_nL.1 a.2).2
      left_inv := fun x => rn_inj (rn_ofN _ (mem_nL.1 (rn_mem_nL x)).1 _)
      right_inv := fun a => Subtype.ext (rn_ofN _ (mem_nL.1 a.2).1 _) }
  rw [Nat.card_congr e, card_subtype_mem nL_nodup, nL_length]

end CFSG.QuasithinUnique.Vol2Native.L239.L33Insp
