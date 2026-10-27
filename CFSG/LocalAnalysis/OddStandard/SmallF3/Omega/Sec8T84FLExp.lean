module

public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace FL

variable {R : Type*} [Ring R]

@[expose] def lin : List (R × R) → R
  | [] => 0
  | (m, Z) :: t => Z * (t.map Prod.fst).prod + m * lin t

theorem prod_expand (h4 : ∀ x : R, (4 : ℕ) • x = 0) (t : List (R × R)) :
    (t.map fun p => p.1 + (2 : ℕ) • p.2).prod = (t.map Prod.fst).prod + (2 : ℕ) • lin t := by
  induction t with
  | nil => simp [lin]
  | cons p t ih =>
    obtain ⟨m, Z⟩ := p
    simp only [List.map_cons, List.prod_cons, lin, ih]
    have h1 : (2 : ℕ) • Z * (2 : ℕ) • lin t = 0 := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
      exact h4 _
    rw [add_mul, mul_add, mul_add, h1, smul_mul_assoc, mul_smul_comm, smul_add]
    abel

section Trace

variable {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]

@[expose] def cX : Matrix n n S → List (Matrix n n S × Bool) → Matrix n n S
  | _, [] => 0
  | W, (m, b) :: t => (if b then (t.map Prod.fst).prod * W else 0) + cX (W * m) t

@[expose] def cY : Matrix n n S → List (Matrix n n S × Bool) → Matrix n n S
  | _, [] => 0
  | W, (m, b) :: t => (if b then 0 else (t.map Prod.fst).prod * W) + cY (W * m) t

theorem trace_lin (ws : List (Matrix n n S × Bool)) (X Y W : Matrix n n S) :
    Matrix.trace (W * lin (ws.map fun p => (p.1, if p.2 then X else Y))) =
      Matrix.trace (cX W ws * X) + Matrix.trace (cY W ws * Y) := by
  induction ws generalizing W with
  | nil => simp [lin, cX, cY]
  | cons p t ih =>
    obtain ⟨m, b⟩ := p
    have e1 : ((t.map fun p => (p.1, if p.2 then X else Y)).map Prod.fst) = t.map Prod.fst := by
      simp [List.map_map, Function.comp_def]
    simp only [List.map_cons, lin, cX, cY, e1, Matrix.mul_add, Matrix.trace_add]
    rw [← mul_assoc W m, ih (W * m), ← mul_assoc W, Matrix.trace_mul_cycle]
    cases b <;> simp [add_mul, Matrix.trace_add] <;> ring

theorem trace_prod_expand (h4 : ∀ x : Matrix n n S, (4 : ℕ) • x = 0)
    (w : List (Matrix n n S × Bool)) (X Y W : Matrix n n S) :
    Matrix.trace (W * (w.map fun p => p.1 + (2 : ℕ) • (if p.2 then X else Y)).prod) =
      Matrix.trace (W * (w.map Prod.fst).prod) +
        (2 : ℕ) • (Matrix.trace (cX W w * X) + Matrix.trace (cY W w * Y)) := by
  have h := prod_expand h4 (w.map fun p => (p.1, if p.2 then X else Y))
  have e1 : (w.map fun p => (p.1, if p.2 then X else Y)).map Prod.fst = w.map Prod.fst := by
    simp [List.map_map, Function.comp_def]
  have e2 : ((w.map fun p => (p.1, if p.2 then X else Y)).map fun p => p.1 + (2 : ℕ) • p.2) =
      w.map fun p => p.1 + (2 : ℕ) • (if p.2 then X else Y) := by
    simp [List.map_map, Function.comp_def]
  rw [e1, e2] at h
  rw [h, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, trace_lin]

end Trace

end FL

end CFSG.OddStandard.SmallF3.Omega
