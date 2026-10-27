module

public import CFSG.CGT.A8S.Words

public section

namespace CFSG.CGT.A8S

@[expose] def relsN0A8 : List (List (Fin 5 × Bool)) :=
  [[(0, true), (0, true)],
   [(1, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
   [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true),
    (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)],
   [(2, true), (2, true)],
   [(2, true), (3, true), (2, false), (3, false)],
   [(2, true), (4, true), (2, false), (4, false)],
   [(3, true), (3, true)],
   [(3, true), (4, true), (3, false), (4, false)],
   [(4, true), (4, true)],
   [(0, false), (2, true), (0, true), (2, false)],
   [(0, false), (3, true), (0, true), (3, false)],
   [(0, false), (4, true), (0, true), (4, false), (2, false)],
   [(1, false), (2, true), (1, true), (3, false)],
   [(1, false), (3, true), (1, true), (4, false)],
   [(1, false), (4, true), (1, true), (2, false)]]

@[expose] def thetaRelsA8 : List A8Word :=
  [[(5, true), (5, true)],
   [(5, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
    (0, true), (1, false), (5, true), (1, true), (0, false), (1, false), (0, false), (1, true),
    (0, false), (1, true), (4, false), (0, false), (1, true)],
   [(5, true), (0, true), (4, true), (1, false), (0, true), (1, true), (5, true), (0, false),
    (1, false), (0, false), (1, true), (0, false), (4, false)]]

@[expose] def ruRelA8 : List A8Word :=
  [[(5, true), (1, true), (5, true), (1, false), (5, true), (0, false), (1, true), (3, false),
    (0, false), (1, false), (0, false)]]

@[expose] def a8Rels : List A8Word := relsN0A8.map liftW5 ++ thetaRelsA8 ++ ruRelA8

@[expose] def a8PermFun : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 5, 4, 7, 6],
    ![0, 4, 1, 5, 2, 6, 3, 7],
    ![1, 0, 3, 2, 5, 4, 7, 6],
    ![2, 3, 0, 1, 6, 7, 4, 5],
    ![4, 5, 6, 7, 0, 1, 2, 3],
    ![4, 7, 5, 6, 0, 2, 3, 1]]

@[expose] def a8PermInvFun : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 5, 4, 7, 6],
    ![0, 2, 4, 6, 1, 3, 5, 7],
    ![1, 0, 3, 2, 5, 4, 7, 6],
    ![2, 3, 0, 1, 6, 7, 4, 5],
    ![4, 5, 6, 7, 0, 1, 2, 3],
    ![4, 7, 5, 6, 0, 2, 3, 1]]

@[expose] def a8Perm (i : Fin 6) : Equiv.Perm (Fin 8) where
  toFun := a8PermFun i
  invFun := a8PermInvFun i
  left_inv := by revert i; decide
  right_inv := by revert i; decide

@[expose] def transl (c : Fin 8) : Equiv.Perm (Fin 8) where
  toFun x := ⟨x.val ^^^ c.val, Nat.xor_lt_two_pow (n := 3) x.isLt c.isLt⟩
  invFun x := ⟨x.val ^^^ c.val, Nat.xor_lt_two_pow (n := 3) x.isLt c.isLt⟩
  left_inv := by revert c; decide
  right_inv := by revert c; decide

@[expose] def dWordA8 : Fin 2 → A8Word :=
  ![[(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
     (1, false)],
    [(0, true), (4, true), (1, false), (0, true), (1, true)]]

@[expose] def thetaWordA8 : Fin 2 → A8Word :=
  ![[(1, false), (0, true), (4, true), (1, false), (0, true), (1, false), (0, true), (1, true),
     (0, true), (1, false)],
    [(4, true), (0, true), (1, false), (0, true), (1, true), (0, true)]]

@[expose] def uWordA8 : A8Word :=
  [(4, true), (1, false), (0, true), (1, true)]

@[expose] def nWordA8 : A8Word :=
  [(1, true)]

@[expose] def wWordA8 : A8Word :=
  [(0, true), (1, true), (0, true), (3, true), (1, false), (0, true)]

@[expose] def bWordA8 : A8Word :=
  [(0, true), (3, true)]

@[expose] def dAWordA8 : A8Word :=
  [(2, true)]

@[expose] def yWordA8 : Fin 3 → A8Word :=
  ![[(0, true), (1, true), (0, true), (2, true), (1, false), (0, true), (1, true), (0, true),
     (1, false)],
    [(1, true), (0, true), (4, true), (1, false), (0, true), (1, true), (0, true), (1, false)],
    [(1, true), (0, true), (2, true), (1, false), (0, true), (1, true), (0, true), (4, true),
     (1, false)]]

@[expose] def fWordA8 : Fin 3 → A8Word :=
  ![[(0, true), (1, true), (0, true), (2, true), (1, false), (0, true), (1, true), (0, true),
     (1, false)],
    [(0, true), (2, true), (3, true)],
    [(0, true), (3, true)]]

@[expose] def wrongWordA8 : Fin 7 → A8Word :=
  ![[(1, true), (4, true), (0, true), (1, false), (0, true)],
    [(0, true), (1, true), (0, true), (4, true), (1, false)],
    [(0, true), (1, true), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (2, true), (1, false)],
    [(1, true), (0, true), (4, true), (1, false), (0, true), (4, true)],
    [(0, true), (1, true), (0, true), (3, true), (4, true), (1, false)],
    [(1, true), (0, true), (2, true), (3, true), (1, false)]]

@[expose] def bGenWordA8 : Fin 2 → A8Word :=
  ![[(0, true), (1, false), (0, true), (1, true), (0, true), (2, true), (1, false), (0, true),
     (1, true)],
    [(0, true), (3, true)]]

@[expose] def aGenWordA8 : Fin 2 → A8Word :=
  ![[(2, true)],
    [(2, true), (3, true)]]

end CFSG.CGT.A8S
