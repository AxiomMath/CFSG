module

public import CFSG.CGT.A8S.L2SubD
public import CFSG.CGT.A8S.L2Eval

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

@[expose] def evD (a b : ℕ) : List (Fin 2) → ℕ
  | [] => 2184
  | l :: w => cmul (if l = 0 then a else b) (evD a b w)

theorem avc_evalD (x y : PG 5 relsN0A8) (w : List (Fin 2)) :
    avc (evalD x y w) = evD (avc x) (avc y) w := by
  induction w with
  | nil => exact avc_one
  | cons l w ih =>
    simp only [evalD, evD]
    rw [avc_mul, ih]
    split <;> rfl

@[expose] def dW5 : Fin 2 → List (Fin 5 × Bool) :=
  ![[(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
     (1, false)],
    [(0, true), (4, true), (1, false), (0, true), (1, true)]]

@[expose] def thW5 : Fin 2 → List (Fin 5 × Bool) :=
  ![[(1, false), (0, true), (4, true), (1, false), (0, true), (1, false), (0, true), (1, true),
     (0, true), (1, false)],
    [(4, true), (0, true), (1, false), (0, true), (1, true), (0, true)]]

theorem liftW5_dW5 (i : Fin 2) : liftW5 (dW5 i) = dWordA8 i := by
  fin_cases i <;> rfl

theorem liftW5_thW5 (i : Fin 2) : liftW5 (thW5 i) = thetaWordA8 i := by
  fin_cases i <;> rfl

abbrev dE (i : Fin 2) : PG 5 relsN0A8 := mkW (dW5 i)

abbrev thE (i : Fin 2) : PG 5 relsN0A8 := mkW (thW5 i)

@[expose] def dC : Fin 2 → ℕ := ![3160, 2717]

@[expose] def thC : Fin 2 → ℕ := ![3675, 3228]

theorem avc_dE (i : Fin 2) : avc (dE i) = dC i := by
  rw [avc_mk]
  revert i
  decide +kernel

theorem avc_thE (i : Fin 2) : avc (thE i) = thC i := by
  rw [avc_mk]
  revert i
  decide +kernel

theorem normB0c_dC_thC : ∀ i : Fin 2, normB0c (dC i) = true ∧ normB0c (thC i) = true := by
  decide +kernel

theorem dE_mem (i : Fin 2) : dE i ∈ D0 :=
  mem_D0_of_normB0c (by rw [avc_dE]; exact (normB0c_dC_thC i).1)

theorem thE_mem (i : Fin 2) : thE i ∈ D0 :=
  mem_D0_of_normB0c (by rw [avc_thE]; exact (normB0c_dC_thC i).2)

theorem avc_evalD_dE (w : List (Fin 2)) :
    avc (evalD (dE 0) (dE 1) w) = evD 3160 2717 w := by
  rw [avc_evalD, avc_dE, avc_dE]
  rfl

end CFSG.CGT.A8S.L2
