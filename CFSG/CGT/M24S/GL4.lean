module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.CGT.M24S.GL4

open Matrix

abbrev e0 : Fin 4 → ZMod 2 := Pi.single 0 1

@[expose] def blk (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  g.submatrix Fin.succ Fin.succ

@[expose] def top (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Fin 3 → ZMod 2 :=
  fun j => g 0 j.succ

@[expose] def tail (w : Fin 4 → ZMod 2) : Fin 3 → ZMod 2 :=
  fun i => w i.succ

@[expose] def mk4 (a : Fin 3 → ZMod 2) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of (Fin.cons (Fin.cons 1 a) fun i => Fin.cons 0 (B i))

@[simp] theorem tail_add (u v : Fin 4 → ZMod 2) : tail (u + v) = tail u + tail v :=
  rfl

@[simp] theorem tail_zero : tail 0 = 0 :=
  rfl

section Block

variable (g g' : Matrix (Fin 4) (Fin 4) (ZMod 2))

theorem mulVec_e0_apply (i : Fin 4) : (g *ᵥ e0) i = g i 0 := by
  rw [mulVec_single_one]
  rfl

theorem apply_zero_zero_of_mulVec_e0 (hg : g *ᵥ e0 = e0) : g 0 0 = 1 := by
  rw [← mulVec_e0_apply g 0, hg]
  rfl

theorem apply_succ_zero_of_mulVec_e0 (hg : g *ᵥ e0 = e0) (i : Fin 3) : g i.succ 0 = 0 := by
  rw [← mulVec_e0_apply g i.succ, hg]
  exact Pi.single_eq_of_ne (Fin.succ_ne_zero i) 1

theorem blk_mul (hg : g *ᵥ e0 = e0) : blk (g * g') = blk g * blk g' := by
  ext i j
  simp only [blk, submatrix_apply, mul_apply, Fin.sum_univ_succ (n := 3),
    apply_succ_zero_of_mulVec_e0 g hg, zero_mul, zero_add]

theorem tail_mulVec (hg : g *ᵥ e0 = e0) (w : Fin 4 → ZMod 2) :
    tail (g *ᵥ w) = blk g *ᵥ tail w := by
  ext i
  simp only [tail, blk, mulVec, dotProduct, submatrix_apply, Fin.sum_univ_succ (n := 3),
    apply_succ_zero_of_mulVec_e0 g hg, zero_mul, zero_add]

theorem top_mul (hg : g *ᵥ e0 = e0) : top (g * g') = top g' + vecMul (top g) (blk g') := by
  ext j
  simp only [top, blk, mul_apply, vecMul, dotProduct, submatrix_apply, Pi.add_apply,
    Fin.sum_univ_succ (n := 3), apply_zero_zero_of_mulVec_e0 g hg, one_mul]

theorem mulVec_apply_zero (hg : g *ᵥ e0 = e0) (w : Fin 4 → ZMod 2) :
    (g *ᵥ w) 0 = w 0 + top g ⬝ᵥ tail w := by
  simp only [mulVec, dotProduct, top, tail, Fin.sum_univ_succ (n := 3),
    apply_zero_zero_of_mulVec_e0 g hg, one_mul]

theorem eq_of_mulVec_e0 (hg : g *ᵥ e0 = e0) (hg' : g' *ᵥ e0 = e0) (hb : blk g = blk g')
    (ht : top g = top g') : g = g' := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rw [apply_zero_zero_of_mulVec_e0 g hg, apply_zero_zero_of_mulVec_e0 g' hg']
  · exact congrFun ht j
  · rw [apply_succ_zero_of_mulVec_e0 g hg, apply_succ_zero_of_mulVec_e0 g' hg']
  · exact congrFun (congrFun hb i) j

end Block

section MkFour

variable (a : Fin 3 → ZMod 2) (B : Matrix (Fin 3) (Fin 3) (ZMod 2))

theorem mk4_mulVec_e0 : mk4 a B *ᵥ e0 = e0 := by
  ext i
  rw [mulVec_e0_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [mk4]

@[simp] theorem blk_mk4 : blk (mk4 a B) = B := by
  ext i j
  simp [blk, mk4]

@[simp] theorem top_mk4 : top (mk4 a B) = a := by
  ext j
  simp [top, mk4]

theorem det_mk4 : (mk4 a B).det = B.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin 3, mk4 a B i.succ 0 = 0 := fun i =>
    apply_succ_zero_of_mulVec_e0 _ (mk4_mulVec_e0 a B) i
  have h1 : (mk4 a B).submatrix (Fin.succAbove 0) Fin.succ = B := by
    ext i j
    simp [mk4]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, h1, Fin.val_zero,
    pow_zero, one_mul]
  rw [apply_zero_zero_of_mulVec_e0 _ (mk4_mulVec_e0 a B), one_mul]

theorem mk4_zero_one : mk4 0 1 = 1 := by
  refine eq_of_mulVec_e0 _ _ (mk4_mulVec_e0 0 1) ?_ ?_ ?_
  · ext i
    rw [mulVec_e0_apply]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp [Fin.succ_ne_zero]
  · rw [blk_mk4]
    ext i j
    simp [blk, one_apply]
  · rw [top_mk4]
    ext j
    simp [top, one_apply, (Fin.succ_ne_zero j).symm]

theorem eq_mk4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg : g *ᵥ e0 = e0) :
    g = mk4 (top g) (blk g) :=
  eq_of_mulVec_e0 _ _ hg (mk4_mulVec_e0 _ _) (blk_mk4 _ _).symm (top_mk4 _ _).symm

@[simp] theorem blk_one : blk 1 = 1 := by
  rw [← mk4_zero_one, blk_mk4]

@[simp] theorem top_one : top 1 = 0 := by
  rw [← mk4_zero_one, top_mk4]

theorem eq_one_of_forall_mulVec_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : ∀ w, M *ᵥ w = w) : M = 1 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at h1
  rw [one_apply]
  by_cases hij : i = j
  · subst hij
    simpa using h1
  · rw [ite_eq_right hij]
    simpa [Pi.single_apply, hij] using h1

end MkFour

section ZModTwo

theorem zmod_two_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem zmod_two_eq_one_of_mul_self : ∀ x : ZMod 2, x * x = 1 → x = 1 := by decide

theorem zmod_two_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

theorem vec_add_self {n : ℕ} (w : Fin n → ZMod 2) : w + w = 0 := by
  ext i
  exact zmod_two_add_self (w i)

theorem det_eq_one_of_mul_self {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : B * B = 1) :
    B.det = 1 := by
  apply zmod_two_eq_one_of_mul_self
  rw [← det_mul, h, det_one]

theorem eq_zero_or_eq_e0_of_tail_eq_zero {w : Fin 4 → ZMod 2} (hw : tail w = 0) :
    w = 0 ∨ w = e0 := by
  have hs : ∀ i : Fin 3, w i.succ = 0 := fun i => congrFun hw i
  rcases zmod_two_eq_zero_or_one (w 0) with h | h
  · left
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact h
    · exact hs i
  · right
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact h
    · rw [hs i]
      exact (Pi.single_eq_of_ne (M := fun _ : Fin 4 => ZMod 2) (Fin.succ_ne_zero i) 1).symm

theorem mat_add_self {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) : M + M = 0 := by
  ext i j
  exact zmod_two_add_self (M i j)

theorem one_add_vecMulVec_mulVec {n : ℕ} (k f w : Fin n → ZMod 2) :
    (1 + vecMulVec k f) *ᵥ w = w + (f ⬝ᵥ w) • k := by
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem vecMul_one_add_vecMulVec {n : ℕ} (k f a : Fin n → ZMod 2) :
    vecMul a (1 + vecMulVec k f) = a + (a ⬝ᵥ k) • f := by
  rw [vecMul_add, vecMul_one, vecMul_vecMulVec]

theorem one_add_vecMulVec_mul_self {n : ℕ} {k f : Fin n → ZMod 2} (h : f ⬝ᵥ k = 0) :
    (1 + vecMulVec k f) * (1 + vecMulVec k f) = 1 := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, h,
    zero_smul, vecMulVec_zero, add_zero, add_assoc, mat_add_self, add_zero]

theorem exists_transvection_aux : ∀ a w : Fin 3 → ZMod 2, a ≠ 0 → w ≠ 0 →
    ∃ k f : Fin 3 → ZMod 2, k ≠ 0 ∧ f ⬝ᵥ k = 0 ∧ a ⬝ᵥ k = 0 ∧ f ⬝ᵥ w = 1 := by
  decide

theorem exists_transvection {a w : Fin 3 → ZMod 2} (ha : a ≠ 0) (hw : w ≠ 0) :
    ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B * B = 1 ∧ vecMul a B = a ∧ B *ᵥ w ≠ w := by
  obtain ⟨k, f, hk, hfk, hak, hfw⟩ := exists_transvection_aux a w ha hw
  refine ⟨1 + vecMulVec k f, one_add_vecMulVec_mul_self hfk, ?_, ?_⟩
  · rw [vecMul_one_add_vecMulVec, hak, zero_smul, add_zero]
  · rw [one_add_vecMulVec_mulVec, hfw, one_smul]
    intro h
    apply hk
    have h1 := congrArg (· + w) h
    simpa only [add_comm w k, add_assoc, vec_add_self, add_zero] using h1

theorem exists_mulVec_eq_e0_aux : ∀ v : Fin 4 → ZMod 2, v ≠ 0 →
    ∃ f : Fin 4 → ZMod 2, f ⬝ᵥ (v + e0) = 0 ∧ f ⬝ᵥ v = 1 := by
  decide

theorem exists_mulVec_eq_e0 {v : Fin 4 → ZMod 2} (hv : v ≠ 0) :
    ∃ A : Matrix (Fin 4) (Fin 4) (ZMod 2), A * A = 1 ∧ A *ᵥ v = e0 := by
  obtain ⟨f, hf, hfv⟩ := exists_mulVec_eq_e0_aux v hv
  refine ⟨1 + vecMulVec (v + e0) f, one_add_vecMulVec_mul_self hf, ?_⟩
  rw [one_add_vecMulVec_mulVec, hfv, one_smul, ← add_assoc, vec_add_self, zero_add]

end ZModTwo

end CFSG.CGT.M24S.GL4
