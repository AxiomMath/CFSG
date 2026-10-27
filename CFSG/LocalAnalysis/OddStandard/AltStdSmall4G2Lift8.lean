module

public import Certificates.Certificate36406
public import Certificates.Data.GrSLitL34FactsFourCubeData

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Matrix

@[expose] noncomputable def red84 :
    Matrix (Fin 3) (Fin 3) (ZMod 8) →+* Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  RingHom.mapMatrix (ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4))

theorem red84_apply (A : Matrix (Fin 3) (Fin 3) (ZMod 8)) (i j : Fin 3) :
    red84 A i j = ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) (A i j) := rfl

theorem red84_X8 : red84 X8 = ComponentClassification.GrSLit.L34Facts.FourCube.X0 := by
  ext i j
  rw [red84_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem red84_Y8 : red84 Y8 = ComponentClassification.GrSLit.L34Facts.FourCube.Y0 := by
  ext i j
  rw [red84_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem red84_fourM (m : Fin 3 → Fin 3 → Bool) : red84 (fourM m) = 0 := by
  ext i j
  rw [red84_apply, fourM, Matrix.of_apply, Matrix.zero_apply]
  split_ifs <;> decide

theorem red84_one_add_fourM (m : Fin 3 → Fin 3 → Bool) : red84 (1 + fourM m) = 1 := by
  rw [map_add, map_one, red84_fourM, add_zero]

private theorem cast_lift8 : ∀ a b : ZMod 8,
    ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) a =
      ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) b →
    a = b + if decide (a ≠ b) then 4 else 0 := by
  decide

theorem eq_add_fourM {A B : Matrix (Fin 3) (Fin 3) (ZMod 8)} (h : red84 A = red84 B) :
    A = B + fourM fun i j => decide (A i j ≠ B i j) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [red84_apply, red84_apply] at hij
  rw [Matrix.add_apply, fourM, Matrix.of_apply]
  exact cast_lift8 _ _ hij

theorem fourM_mul_self (m : Fin 3 → Fin 3 → Bool) : (1 + fourM m) * (1 + fourM m) = 1 := by
  have hEE : fourM m * fourM m = 0 := by
    ext i j
    simp only [fourM, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three, Matrix.zero_apply]
    split_ifs <;> decide
  have h2 : fourM m + fourM m = 0 := by
    ext i j
    simp only [fourM, Matrix.add_apply, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> decide
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, hEE, add_zero, add_assoc, h2,
    add_zero]

@[expose] def conj8 (k k' : Matrix (Fin 3) (Fin 3) (ZMod 8)) (h : k' * k = 1) :
    Matrix (Fin 3) (Fin 3) (ZMod 8) →* Matrix (Fin 3) (Fin 3) (ZMod 8) where
  toFun M := k * M * k'
  map_one' := by
    show k * 1 * k' = 1
    rw [mul_one, mul_eq_one_comm.1 h]
  map_mul' M N := by
    show k * (M * N) * k' = k * M * k' * (k * N * k')
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k' k, h, Matrix.one_mul]

theorem genRel8_conj {X Y k k' : Matrix (Fin 3) (Fin 3) (ZMod 8)} (h : k' * k = 1)
    (hr : GenRel8 X Y) : GenRel8 (k * X * k') (k * Y * k') := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have e : ∀ M, k * M * k' = conj8 k k' h M := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e, ← map_mul, ← map_pow, h1, h2, h3, h4, map_one]

theorem complement8A_holds : complement8A := by
  have h := Certificates.certificate36406
  simp only [lift8Check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem complement8B_holds : complement8B := by
  have h := Certificates.certificate36406
  simp only [lift8Check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem exists_conj_std8 {X Y : Matrix (Fin 3) (Fin 3) (ZMod 8)}
    (hr : GenRel8 X Y) (hX : red84 X = ComponentClassification.GrSLit.L34Facts.FourCube.X0)
    (hY : red84 Y = ComponentClassification.GrSLit.L34Facts.FourCube.Y0) :
    ∃ k k' : Matrix (Fin 3) (Fin 3) (ZMod 8), k * k' = 1 ∧ k' * k = 1 ∧ red84 k = 1 ∧
      k * X * k' = X8 ∧ k * Y * k' = Y8 := by
  have hYe := eq_add_fourM (hY.trans red84_Y8.symm)
  have hY3 : Y * Y * Y = 1 := hr.2.1
  obtain ⟨m1, hm1⟩ := complement8A_holds _ (by rw [← hYe]; exact hY3)
  rw [← hYe] at hm1
  set k1 := 1 + fourM m1 with hk1
  have hk11 := fourM_mul_self m1
  have hY8 : k1 * Y * k1 = Y8 := by rw [hm1, Matrix.mul_assoc, hk11, Matrix.mul_one]
  set X' := k1 * X * k1 with hX'
  have hX'r : red84 X' = red84 X8 := by
    rw [hX', map_mul, map_mul, hk1, red84_one_add_fourM, Matrix.one_mul, Matrix.mul_one, hX,
      red84_X8]
  have hX'e := eq_add_fourM hX'r
  have hrel : GenRel8 X' Y8 := by
    rw [← hY8]
    exact genRel8_conj hk11 hr
  rw [hX'e] at hrel
  obtain ⟨m2, hm2Y, hm2X⟩ := complement8B_holds _ hrel
  rw [← hX'e] at hm2X
  set k2 := 1 + fourM m2 with hk2
  have hk22 := fourM_mul_self m2
  refine ⟨k2 * k1, k1 * k2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc k1 k1, hk11, Matrix.one_mul, hk22]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc k2 k2, hk22, Matrix.one_mul, hk11]
  · rw [map_mul, hk1, hk2, red84_one_add_fourM, red84_one_add_fourM, Matrix.one_mul]
  · calc k2 * k1 * X * (k1 * k2) = k2 * X' * k2 := by rw [hX']; simp only [Matrix.mul_assoc]
      _ = X8 := by rw [hm2X, Matrix.mul_assoc, hk22, Matrix.mul_one]
  · calc k2 * k1 * Y * (k1 * k2) = k2 * (k1 * Y * k1) * k2 := by simp only [Matrix.mul_assoc]
      _ = Y8 := by rw [hY8, hm2Y, Matrix.mul_assoc, hk22, Matrix.mul_one]

end CFSG.OddStandard.AltStdSmall4.G2
