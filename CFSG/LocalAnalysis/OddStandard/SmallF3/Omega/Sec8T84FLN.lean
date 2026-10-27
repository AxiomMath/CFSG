module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FLExp
import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace FL

open scoped Matrix

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 4)

@[expose] def a0 : M4 := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def b0 : M4 := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 1, 1, 1; 1, 1, 1, 0]

def lam1 : M4 := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

def lam2 : M4 := !![1, 1, 1, 1; 0, 0, 0, 0; 0, 0, 1, 1; 0, 0, 0, 0]

def lam3 : M4 := !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

def w1 : List (M4 × Bool) := [(a0, true), (a0, true)]

def w2 : List (M4 × Bool) := [(b0, false), (b0, false), (b0, false)]

def w3 : List (M4 × Bool) :=
  [(a0, true), (b0, false), (a0, true), (b0, false), (a0, true), (b0, false), (a0, true),
    (b0, false), (a0, true), (b0, false)]

theorem farkas_D1 :
    Matrix.trace (lam1ᵀ * (w1.map Prod.fst).prod) + Matrix.trace (lam2ᵀ * (w2.map Prod.fst).prod) +
        Matrix.trace (lam3ᵀ * (w3.map Prod.fst).prod) =
      Matrix.trace lam1ᵀ + Matrix.trace lam2ᵀ + Matrix.trace lam3ᵀ + 2 := by
  decide +kernel

theorem farkas_D2 : (2 : ℕ) • (cX lam1ᵀ w1 + cX lam2ᵀ w2 + cX lam3ᵀ w3) = 0 := by
  decide +kernel

theorem farkas_D3 : (2 : ℕ) • (cY lam1ᵀ w1 + cY lam2ᵀ w2 + cY lam3ᵀ w3) = 0 := by
  decide +kernel

theorem h4_M4 : ∀ x : M4, (4 : ℕ) • x = 0 := by
  intro x
  ext i j
  simp only [Matrix.smul_apply, Matrix.zero_apply, nsmul_eq_mul]
  have : ((4 : ℕ) : ZMod 4) = 0 := by decide
  rw [this, zero_mul]

theorem no_lift_N (X Y : M4) (h1 : (a0 + (2 : ℕ) • X) * (a0 + (2 : ℕ) • X) = 1)
    (h2 : (b0 + (2 : ℕ) • Y) * (b0 + (2 : ℕ) • Y) * (b0 + (2 : ℕ) • Y) = 1)
    (h3 : ((a0 + (2 : ℕ) • X) * (b0 + (2 : ℕ) • Y)) ^ 5 = 1) : False := by
  have t1 := trace_prod_expand h4_M4 w1 X Y lam1ᵀ
  have t2 := trace_prod_expand h4_M4 w2 X Y lam2ᵀ
  have t3 := trace_prod_expand h4_M4 w3 X Y lam3ᵀ
  have p1 : (w1.map fun p => p.1 + (2 : ℕ) • (if p.2 then X else Y)).prod = 1 := by
    simpa [w1] using h1
  have p2 : (w2.map fun p => p.1 + (2 : ℕ) • (if p.2 then X else Y)).prod = 1 := by
    simpa [w2, mul_assoc] using h2
  have p3 : (w3.map fun p => p.1 + (2 : ℕ) • (if p.2 then X else Y)).prod = 1 := by
    simpa [w3, pow_succ, mul_assoc] using h3
  rw [p1, Matrix.mul_one] at t1
  rw [p2, Matrix.mul_one] at t2
  rw [p3, Matrix.mul_one] at t3
  have d2 : (2 : ℕ) • (Matrix.trace (cX lam1ᵀ w1 * X) + Matrix.trace (cX lam2ᵀ w2 * X) +
      Matrix.trace (cX lam3ᵀ w3 * X)) = 0 := by
    rw [← Matrix.trace_add, ← Matrix.trace_add, ← add_mul, ← add_mul, ← Matrix.trace_smul,
      ← smul_mul_assoc, farkas_D2, zero_mul, Matrix.trace_zero]
  have d3 : (2 : ℕ) • (Matrix.trace (cY lam1ᵀ w1 * Y) + Matrix.trace (cY lam2ᵀ w2 * Y) +
      Matrix.trace (cY lam3ᵀ w3 * Y)) = 0 := by
    rw [← Matrix.trace_add, ← Matrix.trace_add, ← add_mul, ← add_mul, ← Matrix.trace_smul,
      ← smul_mul_assoc, farkas_D3, zero_mul, Matrix.trace_zero]
  have d1 := farkas_D1
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at t1 t2 t3 d2 d3
  have h2z : (2 : ZMod 4) = 0 := by
    linear_combination (-1 : ZMod 4) * (t1 + t2 + t3 + d1 + d2 + d3)
  exact absurd h2z (by decide)

end FL

end CFSG.OddStandard.SmallF3.Omega
