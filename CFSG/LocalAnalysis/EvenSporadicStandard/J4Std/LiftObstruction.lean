module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.EvenSporadicStandard.J4Std

@[expose] def maskMatrix (R : Type*) [Zero R] [One R] (m : Fin 11 → ℕ) :
    Matrix (Fin 11) (Fin 11) R :=
  Matrix.of fun i j => if (m i).testBit j then 1 else 0

@[expose] def sRowMasks : Fin 11 → ℕ :=
  ![1592, 280, 1412, 1795, 1506, 1835, 931, 867, 739, 459, 1024]

@[expose] def tRowMasks : Fin 11 → ℕ :=
  ![115, 1915, 957, 32, 1506, 8, 739, 2001, 931, 626, 498]

@[expose] def Smat : Matrix (Fin 11) (Fin 11) (ZMod 2) := maskMatrix (ZMod 2) sRowMasks

@[expose] def Tmat : Matrix (Fin 11) (Fin 11) (ZMod 2) := maskMatrix (ZMod 2) tRowMasks

namespace LiftObstruction

section General

theorem exists_eq_add_two_smul {m n : Type*} (A S : Matrix m n (ZMod 4))
    (h : A.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) =
      S.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2))) :
    ∃ X : Matrix m n (ZMod 4), A = S + (2 : ZMod 4) • X := by
  have key : ∀ u v : ZMod 4, ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) u =
      ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) v → ∃ x : ZMod 4, u = v + 2 * x := by
    decide
  choose X hX using fun i j => key _ _ (congrFun (congrFun h i) j)
  exact ⟨Matrix.of X, by ext i j; simp [hX i j]⟩

variable {n : Type*} [Fintype n]

theorem add_two_smul_mul_add_two_smul (S T X Y : Matrix n n (ZMod 4)) :
    (S + (2 : ZMod 4) • X) * (T + (2 : ZMod 4) • Y) =
      S * T + (2 : ZMod 4) • (X * T + S * Y) := by
  have h : (2 : ZMod 4) * 2 = 0 := by decide
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h,
    zero_smul, smul_add]
  abel

theorem trace_mul_anticomm {R : Type*} [CommSemiring R] (G S X : Matrix n n R) :
    (G * (S * X + X * S)).trace = ((G * S + S * G) * X).trace := by
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.add_mul, Matrix.trace_add, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm (G * X) S, Matrix.mul_assoc S G X]

theorem trace_mul_cross {R : Type*} [CommSemiring R] (H S T X Y : Matrix n n R) :
    (H * (X * T + S * Y)).trace = ((T * H) * X).trace + ((H * S) * Y).trace := by
  rw [Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm (H * X) T, Matrix.mul_assoc T H X]

theorem trace_sq_add_two_smul [DecidableEq n] (G P E : Matrix n n (ZMod 4)) :
    (G * ((P + (2 : ZMod 4) • E) * (P + (2 : ZMod 4) • E) - 1)).trace =
      (G * (P * P - 1)).trace + 2 * ((G * P + P * G) * E).trace := by
  have h1 : P * P + (2 : ZMod 4) • (E * P + P * E) - 1 =
      (P * P - 1) + (2 : ZMod 4) • (P * E + E * P) := by
    rw [add_comm (E * P) (P * E)]; abel
  rw [add_two_smul_mul_add_two_smul, h1, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, trace_mul_anticomm]

theorem two_mul_trace_eq_zero (M X : Matrix n n (ZMod 4)) (h : (2 : ZMod 4) • M = 0) :
    2 * (M * X).trace = 0 := by
  rw [← smul_eq_mul, ← Matrix.trace_smul, ← Matrix.smul_mul, h, Matrix.zero_mul,
    Matrix.trace_zero]

theorem false_of_dual [DecidableEq n] (S T G₁ G₂ G₃ X Y : Matrix n n (ZMod 4))
    (hX : (2 : ZMod 4) • (G₁ * S + S * G₁ + T * (G₃ * (S * T) + (S * T) * G₃)) = 0)
    (hY : (2 : ZMod 4) • (G₂ * T + T * G₂ + (G₃ * (S * T) + (S * T) * G₃) * S) = 0)
    (hc : (G₁ * (S * S - 1)).trace + (G₂ * (T * T - 1)).trace +
      (G₃ * ((S * T) * (S * T) - 1)).trace = 2)
    (hAA : (S + (2 : ZMod 4) • X) * (S + (2 : ZMod 4) • X) = 1)
    (hBB : (T + (2 : ZMod 4) • Y) * (T + (2 : ZMod 4) • Y) = 1)
    (hABAB : ((S + (2 : ZMod 4) • X) * (T + (2 : ZMod 4) • Y)) *
      ((S + (2 : ZMod 4) • X) * (T + (2 : ZMod 4) • Y)) = 1) : False := by
  have key :
      (G₁ * ((S + (2 : ZMod 4) • X) * (S + (2 : ZMod 4) • X) - 1)).trace +
      (G₂ * ((T + (2 : ZMod 4) • Y) * (T + (2 : ZMod 4) • Y) - 1)).trace +
      (G₃ * (((S + (2 : ZMod 4) • X) * (T + (2 : ZMod 4) • Y)) *
        ((S + (2 : ZMod 4) • X) * (T + (2 : ZMod 4) • Y)) - 1)).trace = 2 := by
    rw [add_two_smul_mul_add_two_smul S T X Y, trace_sq_add_two_smul, trace_sq_add_two_smul,
      trace_sq_add_two_smul, trace_mul_cross]
    have hX' := two_mul_trace_eq_zero _ X hX
    have hY' := two_mul_trace_eq_zero _ Y hY
    simp only [Matrix.add_mul, Matrix.trace_add] at hX' hY' ⊢
    linear_combination hc + hX' + hY'
  rw [hAA, hBB, hABAB] at key
  simp only [sub_self, Matrix.mul_zero, Matrix.trace_zero, add_zero] at key
  exact absurd key (by decide)

end General

section Certificate

private def Slift : Matrix (Fin 11) (Fin 11) (ZMod 4) := maskMatrix (ZMod 4) sRowMasks

private def Tlift : Matrix (Fin 11) (Fin 11) (ZMod 4) := maskMatrix (ZMod 4) tRowMasks

private def cert₁ : Matrix (Fin 11) (Fin 11) (ZMod 4) :=
  maskMatrix (ZMod 4) ![11, 3, 3, 0, 0, 8, 0, 11, 0, 11, 0]

private def cert₂ : Matrix (Fin 11) (Fin 11) (ZMod 4) :=
  maskMatrix (ZMod 4) ![3, 3, 8, 8, 0, 11, 0, 8, 0, 3, 0]

private def cert₃ : Matrix (Fin 11) (Fin 11) (ZMod 4) :=
  maskMatrix (ZMod 4) ![0, 3, 0, 11, 0, 0, 0, 3, 0, 0, 0]

private theorem Slift_map :
    Slift.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = Smat := by
  decide

private theorem Tlift_map :
    Tlift.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = Tmat := by
  decide

private theorem dual_X :
    (2 : ZMod 4) • (cert₁ * Slift + Slift * cert₁ +
      Tlift * (cert₃ * (Slift * Tlift) + (Slift * Tlift) * cert₃)) = 0 := by
  decide

private theorem dual_Y :
    (2 : ZMod 4) • (cert₂ * Tlift + Tlift * cert₂ +
      (cert₃ * (Slift * Tlift) + (Slift * Tlift) * cert₃) * Slift) = 0 := by
  decide

private theorem const_two :
    (cert₁ * (Slift * Slift - 1)).trace + (cert₂ * (Tlift * Tlift - 1)).trace +
      (cert₃ * ((Slift * Tlift) * (Slift * Tlift) - 1)).trace = 2 := by
  decide

end Certificate

end LiftObstruction

open LiftObstruction in
theorem no_lift (A B : Matrix (Fin 11) (Fin 11) (ZMod 4))
    (hA : A.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = Smat)
    (hB : B.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) = Tmat)
    (hAA : A * A = 1) (hBB : B * B = 1) (hABAB : (A * B) * (A * B) = 1) : False := by
  obtain ⟨X, rfl⟩ := exists_eq_add_two_smul A Slift (hA.trans Slift_map.symm)
  obtain ⟨Y, rfl⟩ := exists_eq_add_two_smul B Tlift (hB.trans Tlift_map.symm)
  exact false_of_dual Slift Tlift cert₁ cert₂ cert₃ X Y dual_X dual_Y const_two hAA hBB hABAB

end CFSG.EvenSporadicStandard.J4Std
