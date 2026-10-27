module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4EMat
public import Mathlib.Algebra.CharP.Pi
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E

open Matrix

variable {K : Type} [Field K] [CharP K 2]

@[expose] def sel (k i : Fin 2) : Ix := if i = 0 then Sum.inl k else Sum.inr k

theorem plane_sel (k i : Fin 2) : plane (sel k i) = k := by
  unfold sel
  split_ifs <;> rfl

theorem pos_sel (k i : Fin 2) : pos (sel k i) = i := by
  unfold sel
  fin_cases i <;> rfl

theorem sel_plane_pos (a : Ix) : sel (plane a) (pos a) = a := by
  rcases a with i | i <;> fin_cases i <;> rfl

@[expose] def blk (g : Matrix Ix Ix K) (k : Fin 2) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => g (sel k i) (sel k j)

theorem planeMat_blk (g : Matrix Ix Ix K) (h : ∀ a b, plane a ≠ plane b → g a b = 0) :
    planeMat (fun k => blk g k) = g := by
  ext a b
  by_cases hab : plane a = plane b
  · simp only [planeMat, hab, if_true, blk, Matrix.of_apply, pos_sel]
    have h1 : sel (plane b) (pos a) = a := by
      rw [← hab]; exact sel_plane_pos a
    have h2 : sel (plane b) (pos b) = b := sel_plane_pos b
    rw [h1, h2]
  · simp only [planeMat, Matrix.of_apply, hab, if_false]
    exact (h a b hab).symm

theorem planeMat_inj {X Y : Fin 2 → Matrix (Fin 2) (Fin 2) K} (h : planeMat X = planeMat Y) :
    X = Y := by
  funext k
  ext i j
  have := congrFun (congrFun h (sel k i)) (sel k j)
  simpa [planeMat, plane_sel, pos_sel] using this

theorem planeMat_mul (X Y : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    planeMat X * planeMat Y = planeMat fun k => X k * Y k := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, plane, pos]

theorem planeMat_add (X Y : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    planeMat X + planeMat Y = planeMat fun k => X k + Y k := by
  ext a b
  unfold planeMat
  simp only [Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem planeMat_transpose (X : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    (planeMat X)ᵀ = planeMat fun k => (X k)ᵀ := by
  ext a b
  by_cases h : plane a = plane b
  · simp only [planeMat, Matrix.transpose_apply, Matrix.of_apply, if_pos h.symm, if_pos h, h]
  · simp [planeMat, Matrix.transpose_apply, Matrix.of_apply, h, Ne.symm h]

theorem planeMat_one : (1 : Matrix Ix Ix K) = planeMat fun _ => 1 := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeMat, Matrix.one_apply, plane, pos]

@[expose] def J2 (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem JJ_eq_planeMat : JJ K = planeMat fun _ => J2 K := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [JJ, planeMat, J2, plane, pos, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem planeMat_symp_iff (M : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    (planeMat M)ᵀ * JJ K * planeMat M = JJ K ↔ ∀ k, (M k)ᵀ * J2 K * M k = J2 K := by
  rw [JJ_eq_planeMat, planeMat_transpose, planeMat_mul, planeMat_mul]
  constructor
  · intro h k
    exact congrFun (planeMat_inj h) k
  · intro h
    congr 1
    funext k
    exact h k

theorem J2_symp_iff (X : Matrix (Fin 2) (Fin 2) K) : Xᵀ * J2 K * X = J2 K ↔ X.det = 1 := by
  have key : Xᵀ * J2 K * X = X.det • J2 K := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, J2, Matrix.det_fin_two] <;> ring
  rw [key]
  constructor
  · intro h
    have := congrFun (congrFun h 0) 1
    simpa [J2] using this
  · intro h
    rw [h, one_smul]

theorem Pm_planeMat (M : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    Pm (planeMat M) = planeMat fun k => M k * M k + M k + 1 := by
  unfold Pm
  rw [planeMat_one, planeMat_mul, planeMat_add, planeMat_add]

theorem Tmat_quad {c : K} (hc : c ≠ 0) : Tmat c * Tmat c + Tmat c + 1 = 0 := by
  have hc' : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hc'' : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two, hc', hc'', CharTwo.add_self_eq_zero]

theorem Pm_A0 {c : K} (hc : c ≠ 0) : Pm (planeMat ![1, Tmat c]) = planeMat ![1, 0] := by
  rw [Pm_planeMat]
  congr 1
  funext k
  fin_cases k
  · show (1 : Matrix (Fin 2) (Fin 2) K) * 1 + 1 + 1 = 1
    rw [mul_one, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · simp only [Matrix.cons_val_one, Matrix.head_cons]
    exact Tmat_quad hc

theorem commutant_form {c : K} (hc : c ≠ 0) (Y : Matrix (Fin 2) (Fin 2) K)
    (h : Y * Tmat c = Tmat c * Y) : Y = Y 0 0 • 1 + (Y 0 1 * c) • Tmat c := by
  have hc' : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Tmat] at h00 h01
  have e10 : Y 1 0 = c * c * Y 0 1 := by
    linear_combination (-c) * h00 + (-Y 1 0) * hc'
  have e11 : Y 1 1 = Y 0 0 + c * Y 0 1 := by
    linear_combination (-c) * h01 + (Y 0 0 - Y 1 1) * hc'
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Tmat, Matrix.one_apply]
  · simp [Tmat, Matrix.one_apply]
    linear_combination (-Y 0 1) * hc'
  · simp [Tmat, Matrix.one_apply]
    linear_combination e10
  · simp [Tmat, Matrix.one_apply]
    linear_combination e11

theorem cross_zero {c : K} (hc : c ≠ 0) {g : Matrix Ix Ix K}
    (hg : g * planeMat ![1, Tmat c] = planeMat ![1, Tmat c] * g) :
    ∀ a b, plane a ≠ plane b → g a b = 0 := by
  have hgA2 : g * (planeMat ![1, Tmat c] * planeMat ![1, Tmat c]) =
      (planeMat ![1, Tmat c] * planeMat ![1, Tmat c]) * g := by
    rw [← mul_assoc, hg, mul_assoc, hg, ← mul_assoc]
  have hP : g * Pm (planeMat ![1, Tmat c]) = Pm (planeMat ![1, Tmat c]) * g := by
    unfold Pm
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hgA2, hg]
  rw [Pm_A0 hc] at hP
  intro a b hab
  have h := congrFun (congrFun hP a) b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, plane, pos] at h hab ⊢ <;>
    first | exact h | exact h.symm | linear_combination h | linear_combination -h

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
