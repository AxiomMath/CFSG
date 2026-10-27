module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Matrix

private def S0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1,1,0;0,1,0;0,0,1]

private theorem S0_det_ne_zero : S0.det ≠ 0 := by decide +kernel

private def s0 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero S0 S0_det_ne_zero

private theorem s0_val : (s0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = S0 := rfl

private theorem mat_conj (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hM : M * M = 1) (hM1 : M ≠ 1) :
    ∃ C : Matrix (Fin 3) (Fin 3) (ZMod 2), C.det ≠ 0 ∧ C * M = S0 * C := by
  revert M
  decide +kernel

private theorem mk_val (C : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hC : C.det ≠ 0) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero C hC : Matrix (Fin 3) (Fin 3) (ZMod 2)) = C := rfl

private theorem conj_s0 (s : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) (hs : orderOf s = 2) :
    IsConj s s0 := by
  have hsp := (orderOf_eq_prime_iff (x := s) (p := 2)).mp hs
  have hs2 : s ^ 2 = 1 := hsp.1
  have hs1 : s ≠ 1 := hsp.2
  have hsv : (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) * s = 1 := by
    have h := congrArg Units.val hs2
    simpa [pow_two] using h
  have hsv1 : (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := by
    intro h
    exact hs1 (Units.ext h)
  obtain ⟨C, hCdet, hC⟩ := mat_conj s hsv hsv1
  refine isConj_iff.mpr ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet, ?_⟩
  have hcval := mk_val C hCdet
  have hcs : Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet * s = s0 *
      Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet := by
    apply Units.ext
    simp only [Units.val_mul, hcval, s0_val]
    exact hC
  calc Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet * s *
        (Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet)⁻¹
      = s0 * Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet *
        (Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet)⁻¹ := by rw [hcs]
    _ = s0 := by rw [mul_assoc, mul_inv_cancel, mul_one]

theorem involutions_conj_GL32 (s t : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))
    (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t :=
  (conj_s0 s hs).trans (conj_s0 t ht).symm

theorem card_GL32 : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 3]
  norm_num [Fin.prod_univ_three]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
