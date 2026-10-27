module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

@[expose] def twiceHom : ZMod 2 →+ ZMod 4 where
  toFun x := 2 * (x.val : ZMod 4)
  map_zero' := rfl
  map_add' := by decide +kernel

@[expose] def redFour : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

theorem twiceHom_mul (x : ZMod 2) (q : ZMod 4) : twiceHom x * q = twiceHom (x * redFour q) := by
  revert x q
  decide +kernel

theorem mul_twiceHom (q : ZMod 4) (x : ZMod 2) : q * twiceHom x = twiceHom (redFour q * x) := by
  revert x q
  decide +kernel

theorem redFour_twiceHom (x : ZMod 2) : redFour (twiceHom x) = 0 := by
  revert x
  decide +kernel

theorem twiceHom_injective : Function.Injective twiceHom := by
  intro x y
  revert x y
  decide +kernel

@[expose] def liftFour (r : ZMod 2) : ZMod 4 :=
  (r.val : ZMod 4)

theorem redFour_liftFour (r : ZMod 2) : redFour (liftFour r) = r := by
  revert r
  decide +kernel

theorem eq_add_twiceHom (q : ZMod 4) :
    q = liftFour (redFour q) + twiceHom (((q - liftFour (redFour q)).val / 2 : ℕ)) := by
  revert q
  decide +kernel

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem mul_add_twice (P Q : Matrix n n (ZMod 4)) (X Y : Matrix n n (ZMod 2)) :
    (P + X.map twiceHom) * (Q + Y.map twiceHom) =
      P * Q + (X * Q.map redFour + P.map redFour * Y).map twiceHom := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, add_mul, mul_add, twiceHom_mul,
    mul_twiceHom, redFour_twiceHom, zero_mul, map_zero, add_zero,
    Finset.sum_add_distrib, map_add, map_sum]
  abel

omit [Fintype n] [DecidableEq n] in
theorem exists_eq_map_add_twice (P : Matrix n n (ZMod 4)) :
    ∃ X : Matrix n n (ZMod 2), P = (P.map redFour).map liftFour + X.map twiceHom :=
  ⟨Matrix.of fun i j => (((P i j - liftFour (redFour (P i j))).val / 2 : ℕ) : ZMod 2),
    Matrix.ext fun i j => eq_add_twiceHom (P i j)⟩

omit [Fintype n] [DecidableEq n] in
theorem map_liftFour_map_redFour (M : Matrix n n (ZMod 2)) : (M.map liftFour).map redFour = M :=
  Matrix.ext fun i j => redFour_liftFour (M i j)

omit [Fintype n] [DecidableEq n] in
theorem map_twiceHom_injective :
    Function.Injective (fun X : Matrix n n (ZMod 2) => X.map twiceHom) :=
  fun _ _ h => Matrix.ext fun i j => twiceHom_injective (congrFun (congrFun h i) j)

omit [DecidableEq n] in
theorem trace_mul_mul_eq {R : Type*} [CommRing R] (Λ X a : Matrix n n R) :
    trace (Λ * (X * a)) = trace (a * Λ * X) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

omit [DecidableEq n] in
theorem trace_mul_mul_eq' {R : Type*} [CommRing R] (Λ X a : Matrix n n R) :
    trace (Λ * (a * X)) = trace (Λ * a * X) := by
  rw [Matrix.mul_assoc]

@[expose] def kleinFourA : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def kleinFourB : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 1; 0, 1, 1, 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem kleinFourA_mul_self : kleinFourA * kleinFourA = 1 := by
  decide +kernel

theorem kleinFourB_mul_self : kleinFourB * kleinFourB = 1 := by
  decide +kernel

private def kleinDa : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

private def kleinDb : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 0, 1, 1; 0, 0, 0, 0; 0, 0, 0, 0]

private def kleinΛ₁ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0]

private def kleinΛ₂ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 1, 1, 0, 0]

private def kleinΛ₃ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 1, 1, 0, 0; 1, 0, 0, 0]

private theorem klein_liftA_sq :
    kleinFourA.map liftFour * kleinFourA.map liftFour = 1 + kleinDa.map twiceHom := by
  decide +kernel

private theorem klein_liftB_sq :
    kleinFourB.map liftFour * kleinFourB.map liftFour = 1 + kleinDb.map twiceHom := by
  decide +kernel

private theorem klein_lift_comm :
    kleinFourA.map liftFour * kleinFourB.map liftFour =
      kleinFourB.map liftFour * kleinFourA.map liftFour := by
  decide +kernel

private theorem klein_coeffX :
    kleinFourA * kleinΛ₁ + kleinΛ₁ * kleinFourA + kleinFourB * kleinΛ₃ + kleinΛ₃ * kleinFourB =
      0 := by
  decide +kernel

private theorem klein_coeffY :
    kleinFourB * kleinΛ₂ + kleinΛ₂ * kleinFourB + kleinFourA * kleinΛ₃ + kleinΛ₃ * kleinFourA =
      0 := by
  decide +kernel

private theorem klein_const : trace (kleinΛ₁ * kleinDa) + trace (kleinΛ₂ * kleinDb) = 1 := by
  decide +kernel

private theorem eq_zero_of_sq_eq_one {P : Matrix (Fin 4) (Fin 4) (ZMod 4)}
    {D X : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hP : P * P = 1 + D.map twiceHom)
    (h : (P + X.map twiceHom) * (P + X.map twiceHom) = 1) :
    D + (X * P.map redFour + P.map redFour * X) = 0 := by
  apply map_twiceHom_injective
  rw [mul_add_twice, hP, add_assoc] at h
  have h' := add_eq_left.1 h
  show (D + (X * P.map redFour + P.map redFour * X)).map twiceHom =
    (0 : Matrix (Fin 4) (Fin 4) (ZMod 2)).map twiceHom
  rw [Matrix.map_add twiceHom (map_add twiceHom), h', Matrix.map_zero twiceHom (map_zero twiceHom)]

theorem not_exists_lift_kleinFour {A B : Matrix (Fin 4) (Fin 4) (ZMod 4)}
    (hA : A.map redFour = kleinFourA) (hB : B.map redFour = kleinFourB) (hAA : A * A = 1)
    (hBB : B * B = 1) (hAB : A * B = B * A) : False := by
  obtain ⟨X, hX⟩ := exists_eq_map_add_twice A
  obtain ⟨Y, hY⟩ := exists_eq_map_add_twice B
  rw [hA] at hX
  rw [hB] at hY
  subst hX hY
  have hra := map_liftFour_map_redFour kleinFourA
  have hrb := map_liftFour_map_redFour kleinFourB
  have e1 := eq_zero_of_sq_eq_one klein_liftA_sq hAA
  have e2 := eq_zero_of_sq_eq_one klein_liftB_sq hBB
  rw [hra] at e1
  rw [hrb] at e2
  have e3 : X * kleinFourB + kleinFourA * Y = Y * kleinFourA + kleinFourB * X := by
    apply map_twiceHom_injective
    rw [mul_add_twice, mul_add_twice, hra, hrb, klein_lift_comm] at hAB
    exact add_left_cancel hAB
  have t1 : trace (kleinΛ₁ * kleinDa) + (trace (kleinFourA * kleinΛ₁ * X) +
      trace (kleinΛ₁ * kleinFourA * X)) = 0 := by
    have h := congrArg (fun M => trace (kleinΛ₁ * M)) e1
    simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_zero, Matrix.trace_zero] at h
    rwa [trace_mul_mul_eq kleinΛ₁ X kleinFourA, trace_mul_mul_eq' kleinΛ₁ X kleinFourA] at h
  have t2 : trace (kleinΛ₂ * kleinDb) + (trace (kleinFourB * kleinΛ₂ * Y) +
      trace (kleinΛ₂ * kleinFourB * Y)) = 0 := by
    have h := congrArg (fun M => trace (kleinΛ₂ * M)) e2
    simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_zero, Matrix.trace_zero] at h
    rwa [trace_mul_mul_eq kleinΛ₂ Y kleinFourB, trace_mul_mul_eq' kleinΛ₂ Y kleinFourB] at h
  have t3 : trace (kleinFourB * kleinΛ₃ * X) + trace (kleinΛ₃ * kleinFourA * Y) =
      trace (kleinFourA * kleinΛ₃ * Y) + trace (kleinΛ₃ * kleinFourB * X) := by
    have h := congrArg (fun M => trace (kleinΛ₃ * M)) e3
    simp only [Matrix.mul_add, Matrix.trace_add] at h
    rwa [trace_mul_mul_eq kleinΛ₃ X kleinFourB, trace_mul_mul_eq' kleinΛ₃ Y kleinFourA,
      trace_mul_mul_eq kleinΛ₃ Y kleinFourA, trace_mul_mul_eq' kleinΛ₃ X kleinFourB] at h
  have cX : trace (kleinFourA * kleinΛ₁ * X) + trace (kleinΛ₁ * kleinFourA * X) +
      trace (kleinFourB * kleinΛ₃ * X) + trace (kleinΛ₃ * kleinFourB * X) = 0 := by
    have h := congrArg (fun M => trace (M * X)) klein_coeffX
    simpa only [Matrix.add_mul, Matrix.trace_add, Matrix.zero_mul, Matrix.trace_zero] using h
  have cY : trace (kleinFourB * kleinΛ₂ * Y) + trace (kleinΛ₂ * kleinFourB * Y) +
      trace (kleinFourA * kleinΛ₃ * Y) + trace (kleinΛ₃ * kleinFourA * Y) = 0 := by
    have h := congrArg (fun M => trace (M * Y)) klein_coeffY
    simpa only [Matrix.add_mul, Matrix.trace_add, Matrix.zero_mul, Matrix.trace_zero] using h
  have h2 : (2 : ZMod 2) = 0 := rfl
  have h10 : (1 : ZMod 2) = 0 := by
    linear_combination -klein_const + t1 + t2 - cX - cY + t3 +
      (trace (kleinΛ₃ * kleinFourB * X) + trace (kleinFourA * kleinΛ₃ * Y)) * h2
  exact absurd h10 (by decide)

end CFSG.SeitzReduction.LinearPilot
