module

public import CFSG.CGT.T75JM.PAff
public import CFSG.CGT.T75M23.L2FInputs7
public import CFSG.CGT.T75M23.N7Group

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable
open CFSG.CGT.T75JM (V3 glAct FinCheck matD)
open scoped MatrixGroups

@[expose] def glOf7 (m m' : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h1 : m * m' = 1 := by decide)
    (h2 : m' * m = 1 := by decide) : GL (Fin 3) (ZMod 2) := ⟨m, m', h1, h2⟩

@[expose] def idx37 (c : V3) : ℕ := (c 0).val + 2 * (c 1).val + 4 * (c 2).val

@[expose] def eWtab7 : List (List (Fin 2 × Bool)) :=
  [[],
   [(0, true), (0, true), (1, true), (0, true), (0, true), (1, false)],
   [(1, true), (0, true), (0, true), (1, false)],
   [(0, true), (0, true)],
   [(0, true), (1, false), (0, true), (1, false), (0, true), (1, false)],
   [(0, true), (0, true), (1, false), (0, true), (0, true), (1, true)],
   [(1, false), (0, true), (0, true), (1, true)],
   [(0, true), (1, true), (0, false), (1, true), (0, false), (1, true)]]

@[expose] def dWtab7 : List (List (Fin 3 × Bool)) :=
  [[],
   [(2, false), (1, true), (2, true)],
   [(0, true), (1, true), (2, false), (1, true), (0, true), (2, true)],
   [(0, true), (2, true), (0, true), (2, true), (1, true), (2, false)],
   [(1, true), (2, false), (1, true), (2, false)],
   [(1, true), (2, true), (1, true), (2, false), (1, true)],
   [(0, true), (2, true), (0, true), (1, true), (2, true), (1, true), (2, false)],
   [(0, true), (2, true), (0, true), (2, false), (1, true)]]

@[expose] def eW7 (c : V3) : List (Fin 2 × Bool) := eWtab7.getD (idx37 c) []

@[expose] def dW7 (c : V3) : List (Fin 3 × Bool) := dWtab7.getD (idx37 c) []

@[expose] def vExp7 : List (Fin 2 × Bool) → Word6 :=
  subst7 fun p => if p.2 then vGen7 p.1 else invWord7 (vGen7 p.1)

@[expose] def dExp7 : List (Fin 3 × Bool) → Word6 :=
  subst7 fun p => if p.2 then dGen7 p.1 else invWord7 (dGen7 p.1)

@[expose] def thExp7 (k : Fin 2) : List (Fin 3 × Bool) → Word6 :=
  subst7 fun p => if p.2 then thetaW7 k p.1 else invWord7 (thetaW7 k p.1)

@[expose] def castV7 (u : List (Fin 2 × Bool)) : List (Fin 3 × Bool) :=
  u.map fun p => (Fin.castSucc p.1, p.2)

@[expose] def mV17 : GL (Fin 3) (ZMod 2) := glOf7 (!![0, 1, 0; 1, 0, 0; 0, 0, 1])
  (!![0, 1, 0; 1, 0, 0; 0, 0, 1])

@[expose] def mV27 : GL (Fin 3) (ZMod 2) := glOf7 (!![1, 1, 0; 0, 1, 0; 1, 1, 1])
  (!![1, 1, 0; 0, 1, 0; 1, 0, 1])

@[expose] def mG7 : GL (Fin 3) (ZMod 2) := glOf7 (!![1, 0, 0; 1, 0, 1; 1, 1, 0])
  (!![1, 0, 0; 1, 0, 1; 1, 1, 0])

@[expose] def mS7 : GL (Fin 3) (ZMod 2) := glOf7 (!![0, 1, 0; 1, 0, 0; 0, 0, 1])
  (!![0, 1, 0; 1, 0, 0; 0, 0, 1])

@[expose] def mR7 : GL (Fin 3) (ZMod 2) := glOf7 (!![0, 1, 0; 1, 0, 0; 1, 0, 1])
  (!![0, 1, 0; 1, 0, 0; 0, 1, 1])

@[expose] def sV7 : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (0, true), (1, false)]

@[expose] def rV7 : List (Fin 2 × Bool) :=
  [(1, true), (0, false), (1, false), (0, true), (1, false)]

@[expose] def uW7 : List (Fin 3 × Bool) :=
  [(1, true), (0, true), (2, true), (0, true), (1, true), (2, false)]

@[expose] def wA7 : List (Fin 2 × Bool) :=
  [(1, true), (1, true), (0, false), (1, true), (0, true)]

@[expose] def wB7 : List (Fin 2 × Bool) :=
  [(0, false), (1, true), (1, true), (0, true)]

@[expose] def wD07 : List (Fin 2 × Bool) :=
  [(0, true), (0, true), (1, false), (0, true), (0, true), (1, true)]

@[expose] def mv7 : Fin 3 → GL (Fin 3) (ZMod 2) := ![mV17, mV27, mG7]

@[expose] def pRs7a : List (List (Fin 3 × Bool) × List (Fin 3 × Bool)) :=
  [([(2, true), (2, true)], []), ([(2, true)] ++ castV7 wA7 ++ [(2, false)], castV7 wB7)]

@[expose] def pRs7b : List (List (Fin 3 × Bool) × List (Fin 3 × Bool)) :=
  [([(2, true), (2, true)], castV7 wD07)]

@[expose] def pEw7 (j : Fin 3) : List (Fin 3 × Bool) := castV7 (eW7 (Pi.single j 1))

structure PFacts7 : Prop where
  e_mul : ∀ c d : V3, n7 (vExp7 (eW7 c)) * n7 (vExp7 (eW7 d)) = n7 (vExp7 (eW7 (c + d)))
  e_inj : ∀ c d : V3, n7 (vExp7 (eW7 c)) = n7 (vExp7 (eW7 d)) → c = d
  e_cent : ∀ n : N7, (∀ j : Fin 3, n * n7 (vExp7 (eW7 (Pi.single j 1))) =
      n7 (vExp7 (eW7 (Pi.single j 1))) * n) → ∃ c : V3, n = n7 (vExp7 (eW7 c))
  e_tors : ∃ c : V3, c ≠ 0 ∧ n7 (vExp7 (eW7 c)) = n7 [(2, true), (5, true)]
  act_v1 : ∀ c : V3, n7 (vGen7 0) * n7 (vExp7 (eW7 c)) * (n7 (vGen7 0))⁻¹ =
    n7 (vExp7 (eW7 (glAct mV17 c)))
  act_v2 : ∀ c : V3, n7 (vGen7 1) * n7 (vExp7 (eW7 c)) * (n7 (vGen7 1))⁻¹ =
    n7 (vExp7 (eW7 (glAct mV27 c)))
  act_g : ∀ (k : Fin 2) (c : V3), n7 (dExp7 (dW7 c)) = n7 (vExp7 (eW7 c)) ∧
    n7 (thExp7 k (dW7 c)) = n7 (vExp7 (eW7 (glAct mG7 c)))
  theta_rel : n7 (dExp7 uW7) = n7 (vExp7 wA7) ∧ n7 (thExp7 0 uW7) = n7 (vExp7 wB7)
  d0_rel : n7 (d0W7 1) = n7 (vExp7 wD07)
  d8_sq : n7 (vExp7 (sV7 ++ sV7)) = 1
  d8_four : n7 (vExp7 (rV7 ++ rV7 ++ rV7 ++ rV7)) = 1
  d8_conj : n7 (vExp7 (sV7 ++ rV7 ++ sV7 ++ rV7)) = 1
  d8_act_s : ∀ c : V3, n7 (vExp7 sV7) * n7 (vExp7 (eW7 c)) * (n7 (vExp7 sV7))⁻¹ =
    n7 (vExp7 (eW7 (glAct mS7 c)))
  d8_act_r : ∀ c : V3, n7 (vExp7 rV7) * n7 (vExp7 (eW7 c)) * (n7 (vExp7 rV7))⁻¹ =
    n7 (vExp7 (eW7 (glAct mR7 c)))
  d8_dist : ∀ d : DihedralGroup 4, (∀ c, glAct (matD mS7 mR7 d) c = c) → d = 1
  fin0 : FinCheck mv7 pRs7a pEw7 pWords7
  fin1 : FinCheck mv7 pRs7b pEw7 [pEw7 0]

end CFSG.CGT.T75M23
