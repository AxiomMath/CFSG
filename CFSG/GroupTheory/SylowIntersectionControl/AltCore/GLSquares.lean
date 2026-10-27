module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.GroupTheory.AltCore

section Squares

variable {e : ℕ}

private def tvSq {i j : Fin e} (h : i ≠ j) : GL (Fin e) (ZMod 2) :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection h 1)

private theorem coe_tvSq {i j : Fin e} (h : i ≠ j) :
    ((tvSq h : GL (Fin e) (ZMod 2)) : Matrix (Fin e) (Fin e) (ZMod 2)) =
      1 + Matrix.single i j 1 := rfl

private theorem single_add_self (i j : Fin e) :
    Matrix.single i j (1 : ZMod 2) + Matrix.single i j 1 = 0 := by
  rw [← Matrix.single_add, show (1 + 1 : ZMod 2) = 0 from by decide, Matrix.single_zero]

private theorem ring_sq_aux {R : Type*} [Ring R] (a b c : R) (haa : a * a = 0) (hbb : b * b = 0)
    (hba : b * a = 0) (hab : a * b = c) (h2a : a + a = 0) (h2b : b + b = 0) :
    (1 + b) * (1 + a) * ((1 + b) * (1 + a)) = 1 + c := by
  have e1 : (1 + b) * (1 + a) = 1 + a + b := by
    have : (1 + b) * (1 + a) = 1 + a + b + b * a := by noncomm_ring
    rw [this, hba, add_zero]
  have e2 : (1 + a + b) * (1 + a + b) =
      1 + (a + a) + (b + b) + a * a + b * b + b * a + a * b := by noncomm_ring
  rw [e1, e2, haa, hbb, hba, hab, h2a, h2b]
  simp

private theorem tvSq_mul_sq {i j k : Fin e} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) :
    (tvSq hkj * tvSq hik) ^ 2 = tvSq hij := by
  refine Units.ext ?_
  simp only [sq, Units.val_mul, coe_tvSq]
  exact ring_sq_aux _ _ _ (Matrix.single_mul_single_of_ne _ _ _ _ hik.symm _)
    (Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm _)
    (Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _)
    (by rw [Matrix.single_mul_single_same, mul_one]) (single_add_self i k) (single_add_self k j)

private theorem tvSq_sq {i j : Fin e} (h : i ≠ j) : tvSq h ^ 2 = 1 := by
  unfold tvSq
  rw [← map_pow, sq, ← Matrix.SpecialLinearGroup.transvection_add h 1 1,
    show (1 + 1 : ZMod 2) = 0 from by decide, Matrix.SpecialLinearGroup.transvection_coeff_zero,
    map_one]

private theorem tvSq_ne_one {i j : Fin e} (h : i ≠ j) : tvSq h ≠ 1 := by
  intro h1
  have := congrArg (fun g : GL (Fin e) (ZMod 2) => (g : Matrix (Fin e) (Fin e) (ZMod 2)) i j) h1
  simp [coe_tvSq, h] at this

private theorem exists_sq_eq_tvSq (he : 3 ≤ e) {i j : Fin e} (h : i ≠ j) :
    ∃ s : GL (Fin e) (ZMod 2), s ^ 2 = tvSq h := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  exact ⟨_, tvSq_mul_sq h hki.symm hkj⟩

private def InSub (S : Subgroup (GL (Fin e) (ZMod 2))) (N : Matrix (Fin e) (Fin e) (ZMod 2)) :
    Prop :=
  ∃ x ∈ S, (x : Matrix (Fin e) (Fin e) (ZMod 2)) = N

private theorem inSub_diagonal (S : Subgroup (GL (Fin e) (ZMod 2))) (D : Fin e → ZMod 2)
    (hD : (Matrix.diagonal D).det ≠ 0) : InSub S (Matrix.diagonal D) := by
  have hD1 : D = fun _ => 1 := by
    funext i
    have hi : D i ≠ 0 := Finset.prod_ne_zero_iff.mp (by simpa [Matrix.det_diagonal] using hD) i
      (Finset.mem_univ i)
    revert hi
    generalize D i = x
    revert x
    decide
  exact ⟨1, one_mem _, by simp [hD1]⟩

private theorem inSub_transvection {S : Subgroup (GL (Fin e) (ZMod 2))}
    (htv : ∀ {i j : Fin e} (h : i ≠ j), tvSq h ∈ S)
    (t : Matrix.TransvectionStruct (Fin e) (ZMod 2)) : InSub S t.toMatrix := by
  have hc : t.c = 0 ∨ t.c = 1 := by
    generalize t.c = x
    revert x
    decide
  rcases hc with hc | hc
  · exact ⟨1, one_mem _, by simp [Matrix.TransvectionStruct.toMatrix, hc]⟩
  · refine ⟨tvSq t.hij, htv t.hij, ?_⟩
    simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, coe_tvSq, hc]

private theorem inSub_mul {S : Subgroup (GL (Fin e) (ZMod 2))}
    {A B : Matrix (Fin e) (Fin e) (ZMod 2)} (hA : InSub S A) (hB : InSub S B) :
    InSub S (A * B) := by
  obtain ⟨x, hx, rfl⟩ := hA
  obtain ⟨y, hy, rfl⟩ := hB
  exact ⟨x * y, mul_mem hx hy, Units.val_mul x y⟩

private theorem eq_top_of_tvSq_mem {S : Subgroup (GL (Fin e) (ZMod 2))}
    (htv : ∀ {i j : Fin e} (h : i ≠ j), tvSq h ∈ S) : S = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨x, hx, hxg⟩ := Matrix.diagonal_transvection_induction_of_det_ne_zero (InSub S)
    (g : Matrix (Fin e) (Fin e) (ZMod 2)) (Matrix.GeneralLinearGroup.det_ne_zero g)
    (fun D hD => inSub_diagonal S D hD) (inSub_transvection htv)
    (fun A B _ _ hA hB => inSub_mul hA hB)
  rwa [← Units.ext hxg]

end Squares

theorem eq_top_of_sq_mem_GL_two {e : ℕ} (he : 3 ≤ e) {S : Subgroup (GL (Fin e) (ZMod 2))}
    (hS : ∀ g : GL (Fin e) (ZMod 2), g ^ 2 ∈ S) : S = ⊤ := by
  refine eq_top_of_tvSq_mem fun {i j} h => ?_
  obtain ⟨s, hs⟩ := exists_sq_eq_tvSq he h
  rw [← hs]
  exact hS s

theorem exists_sq_ne_one_pow_four_eq_one_GL_two {e : ℕ} (he : 3 ≤ e) :
    ∃ g : GL (Fin e) (ZMod 2), g ^ 2 ≠ 1 ∧ g ^ 4 = 1 := by
  have h01 : (⟨0, by omega⟩ : Fin e) ≠ ⟨1, by omega⟩ := fun h => by simpa using congrArg Fin.val h
  obtain ⟨s, hs⟩ := exists_sq_eq_tvSq he h01
  refine ⟨s, hs ▸ tvSq_ne_one h01, ?_⟩
  rw [show 4 = 2 * 2 from rfl, pow_mul, hs, tvSq_sq]

end CFSG.GroupTheory.AltCore
