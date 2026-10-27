module

public import CFSG.CGT.L5R.RelData

public section

namespace CFSG.CGT.L5R.R3

open CFSG.CGT.M24R

abbrev N0Word : Type := List (Fin 10 × Bool)

@[expose] def inv10 (w : N0Word) : N0Word := w.reverse.map fun p => (p.1, !p.2)

@[expose] def lowerW (w : M24Word) : N0Word :=
  w.filterMap fun p => if h : p.1.val < 10 then some (⟨p.1.val, h⟩, p.2) else none

@[expose] def dW (i : Fin 2) : N0Word := lowerW (dWordL i)

@[expose] def thW (i : Fin 2) : N0Word := lowerW (thetaWordL i)

@[expose] def nW : N0Word := lowerW nWordL

@[expose] def wW : N0Word := lowerW wWordL

@[expose] def bW : N0Word := lowerW bWordL

@[expose] def dAW : N0Word := lowerW dAWordL

@[expose] def yW (j : Fin 2) : N0Word := lowerW (yWordL j)

@[expose] def fW (j : Fin 2) : N0Word := lowerW (fWordL j)

theorem liftW10_dW (i : Fin 2) : liftW10 (dW i) = dWordL i := by
  fin_cases i <;> decide

theorem liftW10_thW (i : Fin 2) : liftW10 (thW i) = thetaWordL i := by
  fin_cases i <;> decide

theorem liftW10_nW : liftW10 nW = nWordL := by decide

theorem liftW10_wW : liftW10 wW = wWordL := by decide

@[expose] def dExp (u : List (Fin 2 × Bool)) : N0Word :=
  u.flatMap fun p => if p.2 then dW p.1 else inv10 (dW p.1)

@[expose] def thExp (u : List (Fin 2 × Bool)) : N0Word :=
  u.flatMap fun p => if p.2 then thW p.1 else inv10 (thW p.1)

@[expose] def uD : List (Fin 2 × Bool) :=
  [(0, true), (0, true), (0, true), (0, true), (1, true), (1, true), (1, true), (0, true),
   (1, true), (0, true), (0, true), (1, true), (0, true)]

@[expose] def bD : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
   (1, true)]

@[expose] def yD : Fin 2 → List (Fin 2 × Bool) :=
  ![[(0, true), (0, true), (0, true), (1, true), (1, true), (0, false), (1, true), (0, false),
     (1, true)],
    [(0, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, true),
     (1, true)]]

@[expose] def a1D : Fin 2 → List (Fin 2 × Bool) :=
  ![[(0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, true), (0, true),
     (1, false)],
    [(0, false), (1, false), (0, true), (1, false), (0, true), (0, true), (1, false),
     (0, false)]]

@[expose] def b1D : Fin 2 → List (Fin 2 × Bool) :=
  ![[(0, false), (1, false), (0, true), (1, false), (0, false), (0, false), (0, false),
     (1, false), (0, true)],
    [(0, true), (0, true), (1, false), (0, false), (1, true), (1, true)]]

end CFSG.CGT.L5R.R3
