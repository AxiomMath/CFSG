module

public import CFSG.CGT.M24R.Words

public section

namespace CFSG.CGT.M24R.R3

abbrev N0Word : Type := List (Fin 10 × Bool)

@[expose] def inv10 (w : N0Word) : N0Word := w.reverse.map fun p => (p.1, !p.2)

@[expose] def dW : Fin 3 → N0Word :=
  ![[(9, true), (0, true), (2, true), (3, false), (5, true), (2, false)],
    [(6, true), (8, true), (2, true), (1, true), (3, true), (5, false), (4, true), (2, false)],
    [(9, true), (0, true), (1, true), (2, true), (5, false), (2, true)]]

@[expose] def thW : Fin 3 → N0Word :=
  ![[(0, true), (3, true), (4, false), (5, true), (3, false)],
    [(6, true), (8, true), (9, true), (2, true), (1, true), (4, true), (2, false)],
    [(0, true), (1, true), (3, true), (4, false), (3, true)]]

@[expose] def nW : N0Word := [(0, true), (4, false), (3, true), (2, false), (0, true), (5, false)]

@[expose] def wW : N0Word := [(6, true), (9, true), (0, true), (4, false), (0, true), (2, false)]

@[expose] def dExp (u : List (Fin 3 × Bool)) : N0Word :=
  u.flatMap fun p => if p.2 then dW p.1 else inv10 (dW p.1)

@[expose] def thExp (u : List (Fin 3 × Bool)) : N0Word :=
  u.flatMap fun p => if p.2 then thW p.1 else inv10 (thW p.1)

@[expose] def uD : List (Fin 3 × Bool) := [(0, false), (2, true), (1, true), (0, false), (1, true)]

@[expose] def bD : List (Fin 3 × Bool) := [(1, true), (1, true)]

@[expose] def aW : N0Word := [(9, true)]

@[expose] def yD : Fin 4 → List (Fin 3 × Bool) :=
  ![[(1, false), (0, true), (2, false), (1, true)],
    [(0, true), (1, true), (1, true), (0, false)],
    [(0, true), (2, true), (0, true), (2, true)],
    [(0, true), (1, false), (0, false), (2, true), (1, false)]]

@[expose] def a1D : Fin 4 → List (Fin 3 × Bool) :=
  ![[(0, true), (2, true), (0, true), (2, true)],
    [(2, true), (0, true), (2, false), (1, true), (0, false), (1, true)],
    [(0, false), (2, false), (1, false), (0, false), (1, true)],
    [(2, true), (0, true), (2, false), (1, false), (0, false), (1, true)]]

@[expose] def b1D : Fin 4 → List (Fin 3 × Bool) :=
  ![[(0, true), (1, true), (2, false), (1, false), (0, true), (1, true), (2, false)],
    [(0, true), (1, true), (0, false), (1, false), (0, true), (1, false)],
    [(0, true), (1, true), (1, true), (0, false), (1, true)],
    [(2, true), (1, true), (2, false), (1, false), (2, true)]]

@[expose] def eW : Fin 16 → N0Word :=
  ![[],
    [(9, true)],
    [(0, true), (1, true)],
    [(9, true), (0, true), (1, true)],
    [(0, true), (2, true), (4, false), (2, true)],
    [(0, true), (3, true), (5, false), (3, true)],
    [(2, true), (1, true), (4, true), (2, false)],
    [(3, true), (1, true), (5, true), (3, false)],
    [(9, true), (0, true), (2, true), (4, false), (2, true)],
    [(9, true), (0, true), (3, true), (5, false), (3, true)],
    [(9, true), (2, true), (1, true), (4, true), (2, false)],
    [(9, true), (3, true), (1, true), (5, true), (3, false)],
    [(2, true), (3, true), (4, true), (5, true), (2, true), (3, true)],
    [(9, true), (2, true), (3, true), (4, true), (5, true), (2, true), (3, true)],
    [(0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (2, true), (3, true)],
    [(9, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (2, true),
      (3, true)]]

@[expose] def tWordOf (v : Fin 16) : N0Word :=
  ((List.finRange 4).filter fun j => v.val.testBit j.val).map fun j =>
    (⟨6 + j.val, by omega⟩, true)

theorem liftW10_dW (i : Fin 3) : liftW10 (dW i) = dWord i := by
  fin_cases i <;> rfl

theorem liftW10_thW (i : Fin 3) : liftW10 (thW i) = thetaWord i := by
  fin_cases i <;> rfl

theorem liftW10_nW : liftW10 nW = nWord := rfl

theorem liftW10_wW : liftW10 wW = wWord := rfl

end CFSG.CGT.M24R.R3
