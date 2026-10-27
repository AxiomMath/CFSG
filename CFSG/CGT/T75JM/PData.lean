module

public import CFSG.CGT.T75JM.Interfaces
public import CFSG.CGT.T75JM.PAff

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable

@[expose] def glOf (m m' : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h1 : m * m' = 1 := by decide)
    (h2 : m' * m = 1 := by decide) : GL (Fin 3) (ZMod 2) := ⟨m, m', h1, h2⟩

@[expose] def idx3 (c : V3) : ℕ := (c 0).val + 2 * (c 1).val + 4 * (c 2).val

@[expose] def eWtab : List (List (Fin 2 × Bool)) :=
  [[],
   [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)],
   [(1, true), (1, true), (0, true), (1, true), (0, true), (1, false)],
   [(0, true), (1, true), (0, true), (1, true)],
   [(1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true)],
   [(0, true), (1, false), (0, false), (1, false), (0, true)],
   [(1, true), (1, true), (0, false), (1, false), (0, false), (1, true)],
   [(1, true), (0, true), (1, true), (0, true)]]

@[expose] def dWtab : List (List (Fin 2 × Bool)) :=
  [[],
   [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true)],
   [(0, true), (0, true)],
   [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true)],
   [(1, true), (0, true), (1, false), (0, false), (1, true)],
   [(1, true), (0, true), (0, true), (1, false), (0, true)],
   [(1, true), (0, false), (1, false), (0, true), (1, true)],
   [(0, true), (1, true), (0, true), (0, true), (1, false)]]

@[expose] def eW (c : V3) : List (Fin 2 × Bool) := eWtab.getD (idx3 c) []

@[expose] def dW (c : V3) : List (Fin 2 × Bool) := dWtab.getD (idx3 c) []

@[expose] def subst {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | a :: u => f a ++ subst f u

@[expose] def vExp : List (Fin 2 × Bool) → List (Fin 6 × Bool) :=
  subst fun p => if p.2 then vGen p.1 else invWord (vGen p.1)

@[expose] def dExp : List (Fin 2 × Bool) → List (Fin 6 × Bool) :=
  subst fun p => if p.2 then dGen p.1 else invWord (dGen p.1)

@[expose] def thExp : List (Fin 2 × Bool) → List (Fin 6 × Bool) :=
  subst fun p => if p.2 then dTheta p.1 else invWord (dTheta p.1)

@[expose] def castV (u : List (Fin 2 × Bool)) : List (Fin 3 × Bool) :=
  u.map fun p => (Fin.castSucc p.1, p.2)

@[expose] def base3 : Fin 3 → M22Word
  | 0 => liftWord (vGen 0)
  | 1 => liftWord (vGen 1)
  | 2 => [(6, true)]

@[expose] def expand3 : List (Fin 3 × Bool) → M22Word :=
  subst fun p => if p.2 then base3 p.1 else invWord (base3 p.1)

@[expose] def val6 (w : List (Fin 6 × Bool)) : PG 6 rels6 := PresentedGroup.mk _ (FreeGroup.mk w)

@[expose] def mV1 : GL (Fin 3) (ZMod 2) := glOf (!![1, 0, 0; 0, 0, 1; 0, 1, 1])
  (!![1, 0, 0; 0, 1, 1; 0, 1, 0])
@[expose] def mV2 : GL (Fin 3) (ZMod 2) := glOf (!![1, 0, 1; 0, 1, 0; 0, 1, 1])
  (!![1, 1, 1; 0, 1, 0; 0, 1, 1])
@[expose] def mG : GL (Fin 3) (ZMod 2) := glOf (!![0, 1, 1; 1, 0, 1; 0, 0, 1])
  (!![0, 1, 1; 1, 0, 1; 0, 0, 1])
@[expose] def mS : GL (Fin 3) (ZMod 2) := glOf (!![1, 0, 1; 0, 1, 0; 0, 0, 1])
  (!![1, 0, 1; 0, 1, 0; 0, 0, 1])
@[expose] def mR : GL (Fin 3) (ZMod 2) := glOf (!![1, 1, 1; 0, 1, 0; 0, 1, 1])
  (!![1, 0, 1; 0, 1, 0; 0, 1, 1])

@[expose] def sV : List (Fin 2 × Bool) := [(0, false), (1, true), (1, true), (0, true)]
@[expose] def rV : List (Fin 2 × Bool) := [(1, false)]
@[expose] def uW : List (Fin 2 × Bool) := [(0, true), (1, true), (1, true), (0, false)]

@[expose] def wA : List (Fin 2 × Bool) := [(0, false), (1, true), (1, true), (0, true)]
@[expose] def wB : List (Fin 2 × Bool) :=
  [(1, true), (1, true), (0, false), (1, true), (0, true)]

@[expose] def mv : Fin 3 → GL (Fin 3) (ZMod 2) := ![mV1, mV2, mG]

@[expose] def pRs : List (List (Fin 3 × Bool) × List (Fin 3 × Bool)) :=
  [([(2, true), (2, true)], []), ([(2, true)] ++ castV wA ++ [(2, true)], castV wB)]

@[expose] def pEw (j : Fin 3) : List (Fin 3 × Bool) := castV (eW (Pi.single j 1))

@[expose] def pWords : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true), (0, true), (1, false), (0, true), (0, false), (1, true)],
   [(0, true), (2, true), (2, true), (0, false), (1, false), (2, false), (2, true), (1, true)],
   [(0, true), (1, true), (2, true), (1, false), (0, false), (2, false), (1, false), (2, false),
    (2, true), (1, true)],
   [(0, true), (1, true), (2, false), (0, false), (1, false), (2, true), (1, false), (0, true),
    (2, false), (1, false)],
   [(0, true), (2, true), (1, true), (2, true), (0, true), (1, false), (2, true), (0, false),
    (2, false), (1, false)]]

theorem pRels_eq : pRels = pWords.map expand3 := by decide +kernel

structure PFacts : Prop where
  e_mul : ∀ c d : V3, val6 (vExp (eW c)) * val6 (vExp (eW d)) = val6 (vExp (eW (c + d)))
  e_inj : ∀ c d : V3, val6 (vExp (eW c)) = val6 (vExp (eW d)) → c = d
  e_cent : ∀ n : PG 6 rels6, (∀ j : Fin 3, n * val6 (vExp (eW (Pi.single j 1))) =
      val6 (vExp (eW (Pi.single j 1))) * n) → ∃ c : V3, n = val6 (vExp (eW c))
  e_tors : ∃ c : V3, c ≠ 0 ∧ val6 (vExp (eW c)) = val6 [(2, true), (3, true), (4, true)]
  act_v1 : ∀ c : V3, val6 (vGen 0) * val6 (vExp (eW c)) * (val6 (vGen 0))⁻¹ =
    val6 (vExp (eW (glAct mV1 c)))
  act_v2 : ∀ c : V3, val6 (vGen 1) * val6 (vExp (eW c)) * (val6 (vGen 1))⁻¹ =
    val6 (vExp (eW (glAct mV2 c)))
  act_g : ∀ c : V3, val6 (dExp (dW c)) = val6 (vExp (eW c)) ∧
    val6 (thExp (dW c)) = val6 (vExp (eW (glAct mG c)))
  theta_rel : val6 (dExp uW) = val6 (vExp wA) ∧ val6 (thExp uW) = val6 (vExp wB)
  d8_sq : val6 (vExp (sV ++ sV)) = 1
  d8_four : val6 (vExp (rV ++ rV ++ rV ++ rV)) = 1
  d8_conj : val6 (vExp (sV ++ rV ++ sV ++ rV)) = 1
  d8_act_s : ∀ c : V3, val6 (vExp sV) * val6 (vExp (eW c)) * (val6 (vExp sV))⁻¹ =
    val6 (vExp (eW (glAct mS c)))
  d8_act_r : ∀ c : V3, val6 (vExp rV) * val6 (vExp (eW c)) * (val6 (vExp rV))⁻¹ =
    val6 (vExp (eW (glAct mR c)))
  d8_dist : ∀ d : DihedralGroup 4, (∀ c, glAct (matD mS mR d) c = c) → d = 1
  fin : FinCheck mv pRs pEw pWords

end CFSG.CGT.T75JM
