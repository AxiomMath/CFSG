module

public import CFSG.GH74.Generic.S1.Defs

public section

namespace CFSG.GH74.Generic.S1

open Matrix

variable {F : Type} [Field F]

@[expose] def gramForm (G : Matrix (Fin 4) (Fin 4) F) (x y : Fin 4 → F) : F := x ⬝ᵥ (G *ᵥ y)

theorem gramForm_comm {G : Matrix (Fin 4) (Fin 4) F} (hG : Gᵀ = G) (x y : Fin 4 → F) :
    gramForm G x y = gramForm G y x := by
  unfold gramForm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG, dotProduct_comm]

theorem mulVec_dotProduct_transpose (a : Matrix (Fin 4) (Fin 4) F) (x w : Fin 4 → F) :
    (a *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (aᵀ *ᵥ w) := by
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec]

theorem gramForm_inv {G a : Matrix (Fin 4) (Fin 4) F} (ha : aᵀ * G * a = G) (x y : Fin 4 → F) :
    gramForm G (a *ᵥ x) (a *ᵥ y) = gramForm G x y := by
  unfold gramForm
  rw [mulVec_dotProduct_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ha]

theorem gramForm_add_left {G : Matrix (Fin 4) (Fin 4) F} (x y w : Fin 4 → F) :
    gramForm G (x + y) w = gramForm G x w + gramForm G y w := by
  unfold gramForm
  rw [add_dotProduct]

theorem gramForm_add_right {G : Matrix (Fin 4) (Fin 4) F} (x y w : Fin 4 → F) :
    gramForm G w (x + y) = gramForm G w x + gramForm G w y := by
  unfold gramForm
  rw [Matrix.mulVec_add, dotProduct_add]

theorem gramForm_neg_right {G : Matrix (Fin 4) (Fin 4) F} (x w : Fin 4 → F) :
    gramForm G w (-x) = - gramForm G w x := by
  unfold gramForm
  rw [Matrix.mulVec_neg, dotProduct_neg]

theorem gramForm_neg_left {G : Matrix (Fin 4) (Fin 4) F} (x w : Fin 4 → F) :
    gramForm G (-x) w = - gramForm G x w := by
  unfold gramForm
  rw [neg_dotProduct]

theorem gramForm_sub_right {G : Matrix (Fin 4) (Fin 4) F} (x y w : Fin 4 → F) :
    gramForm G w (x - y) = gramForm G w x - gramForm G w y := by
  unfold gramForm
  rw [Matrix.mulVec_sub, dotProduct_sub]

theorem gram_matrix_entry (G P : Matrix (Fin 4) (Fin 4) F) (k l : Fin 4) :
    (Pᵀ * G * P) k l = gramForm G (fun r => P r k) (fun r => P r l) := by
  simp only [gramForm, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

theorem gramForm_orth_self {G d z : Matrix (Fin 4) (Fin 4) F} (h2 : (2 : F) ≠ 0) (hGs : Gᵀ = G)
    (hd : dᵀ * G * d = G) (hdd : d * d = z) {x : Fin 4 → F} (hx : z *ᵥ x = -x) :
    gramForm G (d *ᵥ x) x = 0 := by
  have hdd' : d *ᵥ (d *ᵥ x) = -x := by rw [Matrix.mulVec_mulVec, hdd, hx]
  have e : -(d *ᵥ (d *ᵥ x)) = x := by rw [hdd', neg_neg]
  have h1 : gramForm G (d *ᵥ x) x = - gramForm G (d *ᵥ x) (d *ᵥ (d *ᵥ x)) := by
    rw [← gramForm_neg_right, e]
  rw [gramForm_inv hd] at h1
  have h3 : gramForm G (d *ᵥ x) x = - gramForm G (d *ᵥ x) x := by
    rw [gramForm_comm hGs x (d *ᵥ x)] at h1
    exact h1
  have : (2 : F) * gramForm G (d *ᵥ x) x = 0 := by linear_combination h3
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h h2
  · exact h

theorem exists_pair_neg {G z : Matrix (Fin 4) (Fin 4) F} (h2 : (2 : F) ≠ 0) (hGs : Gᵀ = G)
    (hGd : G.det ≠ 0) (hzG : zᵀ * G * z = G) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ u w : Fin 4 → F, z *ᵥ u = -u ∧ z *ᵥ w = -w ∧ gramForm G u w ≠ 0 := by
  have hv : ∃ v : Fin 4 → F, z *ᵥ v ≠ v := by
    by_contra hcon
    push Not at hcon
    apply hz1
    ext i j
    have h1 := congrFun (hcon (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h1
    rw [Matrix.one_apply]
    simpa [Matrix.col_apply, Pi.single_apply] using h1
  obtain ⟨v, hv⟩ := hv
  set u := v - z *ᵥ v with hu
  have hzu : z *ᵥ u = -u := by
    rw [hu, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hz2, Matrix.one_mulVec]
    abel
  have hu0 : u ≠ 0 := by
    intro h
    apply hv
    exact (sub_eq_zero.1 h).symm
  have hGu : G *ᵥ u ≠ 0 := fun h => hu0 (Matrix.eq_zero_of_mulVec_eq_zero hGd h)
  obtain ⟨k, hk⟩ : ∃ k, (G *ᵥ u) k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hGu (funext hcon)
  set w : Fin 4 → F := Pi.single k 1 with hw
  have hGw : gramForm G u w ≠ 0 := by
    have : gramForm G u w = (G *ᵥ u) k := by
      rw [gramForm_comm hGs, gramForm]
      simp [hw]
    rw [this]
    exact hk
  set wm : Fin 4 → F := w - z *ᵥ w with hwm
  have hzw : z *ᵥ wm = -wm := by
    rw [hwm, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hz2, Matrix.one_mulVec]
    abel
  have hC : gramForm G u wm = 2 * gramForm G u w := by
    have h1 : gramForm G u w = gramForm G (z *ᵥ u) (z *ᵥ w) := (gramForm_inv hzG u w).symm
    rw [hzu, gramForm_neg_left] at h1
    rw [hwm, gramForm_sub_right]
    linear_combination (-1 : F) * h1
  refine ⟨u, wm, hzu, hzw, ?_⟩
  rw [hC]
  exact mul_ne_zero h2 hGw

theorem exists_aniso_neg {G z : Matrix (Fin 4) (Fin 4) F} (h2 : (2 : F) ≠ 0) (hGs : Gᵀ = G)
    (hGd : G.det ≠ 0) (hzG : zᵀ * G * z = G) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ x : Fin 4 → F, z *ᵥ x = -x ∧ gramForm G x x ≠ 0 := by
  obtain ⟨u, wm, hzu, hzw, hCne⟩ := exists_pair_neg h2 hGs hGd hzG hz2 hz1
  by_contra hall
  push Not at hall
  have e1 := hall u hzu
  have e2 := hall wm hzw
  have hzs : z *ᵥ (u + wm) = -(u + wm) := by
    rw [Matrix.mulVec_add, hzu, hzw]
    abel
  have e3 := hall (u + wm) hzs
  rw [gramForm_add_left, gramForm_add_right, gramForm_add_right, e1, e2,
    gramForm_comm hGs wm u] at e3
  apply hCne
  have : (2 : F) * gramForm G u wm = 0 := by linear_combination e3
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h h2
  · exact h

theorem neg_stable {z d : Matrix (Fin 4) (Fin 4) F} (hd : z * d = d * z) {y : Fin 4 → F}
    (hy : z *ᵥ y = -y) : z *ᵥ (d *ᵥ y) = -(d *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, hd, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_neg]

@[expose] def q8Frame (a b : Matrix (Fin 4) (Fin 4) F) (x : Fin 4 → F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun r k => (![x, a *ᵥ x, b *ᵥ x, (a * b) *ᵥ x] k) r

theorem q8Frame_gram {G a b z : Matrix (Fin 4) (Fin 4) F} (h2 : (2 : F) ≠ 0) (hGs : Gᵀ = G)
    (hGa : aᵀ * G * a = G) (hGb : bᵀ * G * b = G) (ha2 : a * a = z) (hb2 : b * b = z)
    (hz2 : z * z = 1) (hab : a * b = z * (b * a)) {x : Fin 4 → F} (hx : z *ᵥ x = -x) :
    (q8Frame a b x)ᵀ * G * q8Frame a b x = gramForm G x x • (1 : Matrix (Fin 4) (Fin 4) F) := by
  have hza : z * a = a * z := by rw [← ha2, Matrix.mul_assoc]
  have hzb : z * b = b * z := by rw [← hb2, Matrix.mul_assoc]
  have hba : b * a = z * (a * b) := by
    rw [hab, ← Matrix.mul_assoc, hz2, Matrix.one_mul]
  have hcG : (a * b)ᵀ * G * (a * b) = G := by
    rw [Matrix.transpose_mul]
    calc bᵀ * aᵀ * G * (a * b) = bᵀ * (aᵀ * G * a) * b := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hGa, hGb]
  have hcc : (a * b) * (a * b) = z := by
    calc (a * b) * (a * b) = a * (b * a) * b := by simp only [Matrix.mul_assoc]
      _ = a * (z * (a * b)) * b := by rw [hba]
      _ = (a * z) * a * (b * b) := by simp only [Matrix.mul_assoc]
      _ = (z * a) * a * z := by rw [← hza, hb2]
      _ = z * (a * a) * z := by simp only [Matrix.mul_assoc]
      _ = z * z * z := by rw [ha2]
      _ = z := by rw [hz2, Matrix.one_mul]
  set β := gramForm G x x with hβ
  have hxa : z *ᵥ (a *ᵥ x) = -(a *ᵥ x) := neg_stable hza hx
  have hxb : z *ᵥ (b *ᵥ x) = -(b *ᵥ x) := neg_stable hzb hx
  have hcx : (a * b) *ᵥ x = a *ᵥ (b *ᵥ x) := by rw [Matrix.mulVec_mulVec]
  have oa : gramForm G (a *ᵥ x) x = 0 := gramForm_orth_self h2 hGs hGa ha2 hx
  have ob : gramForm G (b *ᵥ x) x = 0 := gramForm_orth_self h2 hGs hGb hb2 hx
  have oc : gramForm G ((a * b) *ᵥ x) x = 0 := gramForm_orth_self h2 hGs hcG hcc hx
  have haa : ∀ y : Fin 4 → F, z *ᵥ y = -y → y = -(a *ᵥ (a *ᵥ y)) := by
    intro y hy
    rw [Matrix.mulVec_mulVec, ha2, hy, neg_neg]
  have o_ab : gramForm G (a *ᵥ x) (b *ᵥ x) = 0 := by
    have h1 := haa (b *ᵥ x) hxb
    calc gramForm G (a *ᵥ x) (b *ᵥ x) = gramForm G (a *ᵥ x) (-(a *ᵥ (a *ᵥ (b *ᵥ x)))) := by
          rw [← h1]
      _ = - gramForm G x (a *ᵥ (b *ᵥ x)) := by rw [gramForm_neg_right, gramForm_inv hGa]
      _ = - gramForm G ((a * b) *ᵥ x) x := by rw [← hcx, gramForm_comm hGs]
      _ = 0 := by rw [oc, neg_zero]
  have o_ac : gramForm G (a *ᵥ x) ((a * b) *ᵥ x) = 0 := by
    rw [hcx, gramForm_inv hGa, gramForm_comm hGs, ob]
  have hcx' : (a * b) *ᵥ x = -(b *ᵥ (a *ᵥ x)) := by
    have hab' : a * b = z * (b * a) := hab
    have hbax : z *ᵥ (b *ᵥ (a *ᵥ x)) = -(b *ᵥ (a *ᵥ x)) := neg_stable hzb hxa
    rw [hab', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hbax
  have o_bc : gramForm G (b *ᵥ x) ((a * b) *ᵥ x) = 0 := by
    rw [hcx', gramForm_neg_right, gramForm_inv hGb, gramForm_comm hGs, oa, neg_zero]
  have n_a : gramForm G (a *ᵥ x) (a *ᵥ x) = β := gramForm_inv hGa x x
  have n_b : gramForm G (b *ᵥ x) (b *ᵥ x) = β := gramForm_inv hGb x x
  have n_c : gramForm G ((a * b) *ᵥ x) ((a * b) *ᵥ x) = β := gramForm_inv hcG x x
  let v : Fin 4 → Fin 4 → F := ![x, a *ᵥ x, b *ᵥ x, (a * b) *ᵥ x]
  have hg : ∀ k l : Fin 4, gramForm G (v k) (v l) = if k = l then β else 0 := by
    intro k l
    fin_cases k <;> fin_cases l
    · simp [v, hβ]
    · simp only [v]
      rw [gramForm_comm hGs]
      simpa using oa
    · simp only [v]
      rw [gramForm_comm hGs]
      simpa using ob
    · simp only [v]
      rw [gramForm_comm hGs]
      simpa using oc
    · simpa [v] using oa
    · simpa [v] using n_a
    · simpa [v] using o_ab
    · simpa [v] using o_ac
    · simpa [v] using ob
    · simp only [v]
      rw [gramForm_comm hGs]
      simpa using o_ab
    · simpa [v] using n_b
    · simpa [v] using o_bc
    · simpa [v] using oc
    · simp only [v]
      rw [gramForm_comm hGs]
      simpa using o_ac
    · simp only [v]
      rw [gramForm_comm hGs]
      simpa using o_bc
    · simpa [v] using n_c
  ext k l
  rw [gram_matrix_entry]
  have := hg k l
  simp only [v] at this
  simp only [q8Frame, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [show (fun r => (![x, a *ᵥ x, b *ᵥ x, (a * b) *ᵥ x] k) r) =
      ![x, a *ᵥ x, b *ᵥ x, (a * b) *ᵥ x] k from rfl,
    show (fun r => (![x, a *ᵥ x, b *ᵥ x, (a * b) *ᵥ x] l) r) =
      ![x, a *ᵥ x, b *ᵥ x, (a * b) *ᵥ x] l from rfl, this]
  split_ifs <;> simp

theorem no_q8_isometry {G a b z : Matrix (Fin 4) (Fin 4) F} (h2 : (2 : F) ≠ 0)
    (hGs : Gᵀ = G) (hGd : ¬ IsSquare G.det)
    (hGa : aᵀ * G * a = G) (hGb : bᵀ * G * b = G)
    (ha2 : a * a = z) (hb2 : b * b = z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hab : a * b = z * (b * a)) : False := by
  have hG0 : G.det ≠ 0 := fun h => hGd ⟨0, by rw [h]; ring⟩
  have hzG : zᵀ * G * z = G := by
    rw [← ha2, Matrix.transpose_mul]
    calc aᵀ * aᵀ * G * (a * a) = aᵀ * (aᵀ * G * a) * a := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hGa, hGa]
  obtain ⟨x, hx, hxn⟩ := exists_aniso_neg h2 hGs hG0 hzG hz2 hz1
  have hPG := q8Frame_gram h2 hGs hGa hGb ha2 hb2 hz2 hab hx
  set β := gramForm G x x with hβ
  set P := q8Frame a b x with hP
  have hdet : G.det * P.det ^ 2 = β ^ 4 := by
    have h1 := congrArg Matrix.det hPG
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one] at h1
    simp only [Fintype.card_fin, mul_one] at h1
    linear_combination h1
  have hP0 : P.det ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
    exact hxn ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).1 hdet.symm)
  apply hGd
  refine ⟨β ^ 2 / P.det, ?_⟩
  field_simp
  linear_combination hdet

end CFSG.GH74.Generic.S1
