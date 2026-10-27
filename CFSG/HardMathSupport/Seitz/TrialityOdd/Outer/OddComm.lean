module

public import CFSG.RankThree.PartOne.SEITZ7.D4Swap

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZ7
open scoped commutatorElement

variable {K : Type} [Field K]

theorem xd_neg_odd (p : ℕ) (c : K) : xd p (-c) = (xd p c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← xd_add, neg_add_cancel, xd_zero])

theorem xd_inv_odd (p : ℕ) (c : K) : (xd p c)⁻¹ = xd p (-c) := (xd_neg_odd p c).symm

theorem swap_genO {b a c : ℕ} {ε : ℤ}
    (h : RootOps.repCheck d4 b a [(1, 1, c, ε)] = true) (x y : K) :
    xd b y * xd a x = xd c ((ε : K) * (x * y)) * (xd a x * xd b y) := by
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := d4) (K := K) h y x
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] at this
  refine swap_of_comm' _ _ _ ?_
  rw [this]
  congr 1
  ring

theorem commute_genO {b a : ℕ} (h : RootOps.repCheck d4 b a [] = true) (x y : K) :
    Commute (xd b x) (xd a y) := by
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := d4) (K := K) h x y
  simp only [List.map_nil, List.prod_nil] at this
  exact commutatorElement_eq_one_iff_commute.1 this

theorem swapO_0_2 (x y : K) :
    xd 0 y * xd 2 x = xd 5 (-(x * y)) * (xd 2 x * xd 0 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_1_2 (x y : K) :
    xd 1 y * xd 2 x = xd 7 (-(x * y)) * (xd 2 x * xd 1 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_3_2 (x y : K) :
    xd 3 y * xd 2 x = xd 9 (x * y) * (xd 2 x * xd 3 y) :=
  by simpa using swap_genO (ε := 1) (by decide +kernel) x y

theorem swapO_5_1 (x y : K) :
    xd 5 y * xd 1 x = xd 12 (-(x * y)) * (xd 1 x * xd 5 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_5_3 (x y : K) :
    xd 5 y * xd 3 x = xd 13 (-(x * y)) * (xd 3 x * xd 5 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_7_0 (x y : K) :
    xd 7 y * xd 0 x = xd 12 (-(x * y)) * (xd 0 x * xd 7 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_7_3 (x y : K) :
    xd 7 y * xd 3 x = xd 15 (-(x * y)) * (xd 3 x * xd 7 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_9_0 (x y : K) :
    xd 9 y * xd 0 x = xd 13 (x * y) * (xd 0 x * xd 9 y) :=
  by simpa using swap_genO (ε := 1) (by decide +kernel) x y

theorem swapO_9_1 (x y : K) :
    xd 9 y * xd 1 x = xd 15 (x * y) * (xd 1 x * xd 9 y) :=
  by simpa using swap_genO (ε := 1) (by decide +kernel) x y

theorem swapO_12_3 (x y : K) :
    xd 12 y * xd 3 x = xd 19 (-(x * y)) * (xd 3 x * xd 12 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_12_9 (x y : K) :
    xd 12 y * xd 9 x = xd 22 (x * y) * (xd 9 x * xd 12 y) :=
  by simpa using swap_genO (ε := 1) (by decide +kernel) x y

theorem swapO_13_1 (x y : K) :
    xd 13 y * xd 1 x = xd 19 (-(x * y)) * (xd 1 x * xd 13 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_13_7 (x y : K) :
    xd 13 y * xd 7 x = xd 22 (-(x * y)) * (xd 7 x * xd 13 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_15_0 (x y : K) :
    xd 15 y * xd 0 x = xd 19 (-(x * y)) * (xd 0 x * xd 15 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_15_5 (x y : K) :
    xd 15 y * xd 5 x = xd 22 (-(x * y)) * (xd 5 x * xd 15 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem swapO_19_2 (x y : K) :
    xd 19 y * xd 2 x = xd 22 (-(x * y)) * (xd 2 x * xd 19 y) :=
  by simpa using swap_genO (ε := -1) (by decide +kernel) x y

theorem commuteO_1_0 (x y : K) : Commute (xd 1 x) (xd 0 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_3_0 (x y : K) : Commute (xd 3 x) (xd 0 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_3_1 (x y : K) : Commute (xd 3 x) (xd 1 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_5_2 (x y : K) : Commute (xd 5 x) (xd 2 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_5_0 (x y : K) : Commute (xd 5 x) (xd 0 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_7_2 (x y : K) : Commute (xd 7 x) (xd 2 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_7_1 (x y : K) : Commute (xd 7 x) (xd 1 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_7_5 (x y : K) : Commute (xd 7 x) (xd 5 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_9_2 (x y : K) : Commute (xd 9 x) (xd 2 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_9_3 (x y : K) : Commute (xd 9 x) (xd 3 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_9_5 (x y : K) : Commute (xd 9 x) (xd 5 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_9_7 (x y : K) : Commute (xd 9 x) (xd 7 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_12_2 (x y : K) : Commute (xd 12 x) (xd 2 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_12_0 (x y : K) : Commute (xd 12 x) (xd 0 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_12_1 (x y : K) : Commute (xd 12 x) (xd 1 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_12_5 (x y : K) : Commute (xd 12 x) (xd 5 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_12_7 (x y : K) : Commute (xd 12 x) (xd 7 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_13_2 (x y : K) : Commute (xd 13 x) (xd 2 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_13_0 (x y : K) : Commute (xd 13 x) (xd 0 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_13_3 (x y : K) : Commute (xd 13 x) (xd 3 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_13_5 (x y : K) : Commute (xd 13 x) (xd 5 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_13_9 (x y : K) : Commute (xd 13 x) (xd 9 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_13_12 (x y : K) : Commute (xd 13 x) (xd 12 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_15_2 (x y : K) : Commute (xd 15 x) (xd 2 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_15_1 (x y : K) : Commute (xd 15 x) (xd 1 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_15_3 (x y : K) : Commute (xd 15 x) (xd 3 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_15_7 (x y : K) : Commute (xd 15 x) (xd 7 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_15_9 (x y : K) : Commute (xd 15 x) (xd 9 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_15_12 (x y : K) : Commute (xd 15 x) (xd 12 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_15_13 (x y : K) : Commute (xd 15 x) (xd 13 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_0 (x y : K) : Commute (xd 19 x) (xd 0 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_1 (x y : K) : Commute (xd 19 x) (xd 1 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_3 (x y : K) : Commute (xd 19 x) (xd 3 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_5 (x y : K) : Commute (xd 19 x) (xd 5 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_7 (x y : K) : Commute (xd 19 x) (xd 7 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_9 (x y : K) : Commute (xd 19 x) (xd 9 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_12 (x y : K) : Commute (xd 19 x) (xd 12 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_13 (x y : K) : Commute (xd 19 x) (xd 13 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_19_15 (x y : K) : Commute (xd 19 x) (xd 15 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_2 (x y : K) : Commute (xd 22 x) (xd 2 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_0 (x y : K) : Commute (xd 22 x) (xd 0 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_1 (x y : K) : Commute (xd 22 x) (xd 1 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_3 (x y : K) : Commute (xd 22 x) (xd 3 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_5 (x y : K) : Commute (xd 22 x) (xd 5 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_7 (x y : K) : Commute (xd 22 x) (xd 7 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_9 (x y : K) : Commute (xd 22 x) (xd 9 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_12 (x y : K) : Commute (xd 22 x) (xd 12 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_13 (x y : K) : Commute (xd 22 x) (xd 13 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_15 (x y : K) : Commute (xd 22 x) (xd 15 y) :=
  commute_genO (by decide +kernel) x y

theorem commuteO_22_19 (x y : K) : Commute (xd 22 x) (xd 19 y) :=
  commute_genO (by decide +kernel) x y

section Collection

theorem xd_mergeO (p : ℕ) (c d : K) (z : adjointGroup d4 K) :
    xd p c * (xd p d * z) = xd p (c + d) * z := by
  rw [← mul_assoc, ← xd_add]

theorem xd_mergeO' (p : ℕ) (c d : K) : xd p c * xd p d = xd p (c + d) := (xd_add p c d).symm

theorem comm_tailO {p q : ℕ} {x y : K} (h : Commute (xd p x) (xd q y))
    (z : adjointGroup d4 K) : xd p x * (xd q y * z) = xd q y * (xd p x * z) := by
  rw [← mul_assoc, h.eq, mul_assoc]

theorem swap_tailO {p q r : ℕ} {x y : K} {c : K}
    (h : xd p x * xd q y = xd r c * (xd q y * xd p x)) (z : adjointGroup d4 K) :
    xd p x * (xd q y * z) = xd r c * (xd q y * (xd p x * z)) := by
  rw [← mul_assoc, h]
  simp only [mul_assoc]

theorem tailO_1_0 (x y : K) (z : adjointGroup d4 K) :
    xd 1 x * (xd 0 y * z) = xd 0 y * (xd 1 x * z) :=
  comm_tailO (commuteO_1_0 x y) z
theorem endO_1_0 (x y : K) : xd 1 x * xd 0 y = xd 0 y * xd 1 x :=
  (commuteO_1_0 x y).eq

theorem tailO_3_0 (x y : K) (z : adjointGroup d4 K) :
    xd 3 x * (xd 0 y * z) = xd 0 y * (xd 3 x * z) :=
  comm_tailO (commuteO_3_0 x y) z
theorem endO_3_0 (x y : K) : xd 3 x * xd 0 y = xd 0 y * xd 3 x :=
  (commuteO_3_0 x y).eq

theorem tailO_3_1 (x y : K) (z : adjointGroup d4 K) :
    xd 3 x * (xd 1 y * z) = xd 1 y * (xd 3 x * z) :=
  comm_tailO (commuteO_3_1 x y) z
theorem endO_3_1 (x y : K) : xd 3 x * xd 1 y = xd 1 y * xd 3 x :=
  (commuteO_3_1 x y).eq

theorem tailO_5_2 (x y : K) (z : adjointGroup d4 K) :
    xd 5 x * (xd 2 y * z) = xd 2 y * (xd 5 x * z) :=
  comm_tailO (commuteO_5_2 x y) z
theorem endO_5_2 (x y : K) : xd 5 x * xd 2 y = xd 2 y * xd 5 x :=
  (commuteO_5_2 x y).eq

theorem tailO_5_0 (x y : K) (z : adjointGroup d4 K) :
    xd 5 x * (xd 0 y * z) = xd 0 y * (xd 5 x * z) :=
  comm_tailO (commuteO_5_0 x y) z
theorem endO_5_0 (x y : K) : xd 5 x * xd 0 y = xd 0 y * xd 5 x :=
  (commuteO_5_0 x y).eq

theorem tailO_7_2 (x y : K) (z : adjointGroup d4 K) :
    xd 7 x * (xd 2 y * z) = xd 2 y * (xd 7 x * z) :=
  comm_tailO (commuteO_7_2 x y) z
theorem endO_7_2 (x y : K) : xd 7 x * xd 2 y = xd 2 y * xd 7 x :=
  (commuteO_7_2 x y).eq

theorem tailO_7_1 (x y : K) (z : adjointGroup d4 K) :
    xd 7 x * (xd 1 y * z) = xd 1 y * (xd 7 x * z) :=
  comm_tailO (commuteO_7_1 x y) z
theorem endO_7_1 (x y : K) : xd 7 x * xd 1 y = xd 1 y * xd 7 x :=
  (commuteO_7_1 x y).eq

theorem tailO_7_5 (x y : K) (z : adjointGroup d4 K) :
    xd 7 x * (xd 5 y * z) = xd 5 y * (xd 7 x * z) :=
  comm_tailO (commuteO_7_5 x y) z
theorem endO_7_5 (x y : K) : xd 7 x * xd 5 y = xd 5 y * xd 7 x :=
  (commuteO_7_5 x y).eq

theorem tailO_9_2 (x y : K) (z : adjointGroup d4 K) :
    xd 9 x * (xd 2 y * z) = xd 2 y * (xd 9 x * z) :=
  comm_tailO (commuteO_9_2 x y) z
theorem endO_9_2 (x y : K) : xd 9 x * xd 2 y = xd 2 y * xd 9 x :=
  (commuteO_9_2 x y).eq

theorem tailO_9_3 (x y : K) (z : adjointGroup d4 K) :
    xd 9 x * (xd 3 y * z) = xd 3 y * (xd 9 x * z) :=
  comm_tailO (commuteO_9_3 x y) z
theorem endO_9_3 (x y : K) : xd 9 x * xd 3 y = xd 3 y * xd 9 x :=
  (commuteO_9_3 x y).eq

theorem tailO_9_5 (x y : K) (z : adjointGroup d4 K) :
    xd 9 x * (xd 5 y * z) = xd 5 y * (xd 9 x * z) :=
  comm_tailO (commuteO_9_5 x y) z
theorem endO_9_5 (x y : K) : xd 9 x * xd 5 y = xd 5 y * xd 9 x :=
  (commuteO_9_5 x y).eq

theorem tailO_9_7 (x y : K) (z : adjointGroup d4 K) :
    xd 9 x * (xd 7 y * z) = xd 7 y * (xd 9 x * z) :=
  comm_tailO (commuteO_9_7 x y) z
theorem endO_9_7 (x y : K) : xd 9 x * xd 7 y = xd 7 y * xd 9 x :=
  (commuteO_9_7 x y).eq

theorem tailO_12_2 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 2 y * z) = xd 2 y * (xd 12 x * z) :=
  comm_tailO (commuteO_12_2 x y) z
theorem endO_12_2 (x y : K) : xd 12 x * xd 2 y = xd 2 y * xd 12 x :=
  (commuteO_12_2 x y).eq

theorem tailO_12_0 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 0 y * z) = xd 0 y * (xd 12 x * z) :=
  comm_tailO (commuteO_12_0 x y) z
theorem endO_12_0 (x y : K) : xd 12 x * xd 0 y = xd 0 y * xd 12 x :=
  (commuteO_12_0 x y).eq

theorem tailO_12_1 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 1 y * z) = xd 1 y * (xd 12 x * z) :=
  comm_tailO (commuteO_12_1 x y) z
theorem endO_12_1 (x y : K) : xd 12 x * xd 1 y = xd 1 y * xd 12 x :=
  (commuteO_12_1 x y).eq

theorem tailO_12_5 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 5 y * z) = xd 5 y * (xd 12 x * z) :=
  comm_tailO (commuteO_12_5 x y) z
theorem endO_12_5 (x y : K) : xd 12 x * xd 5 y = xd 5 y * xd 12 x :=
  (commuteO_12_5 x y).eq

theorem tailO_12_7 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 7 y * z) = xd 7 y * (xd 12 x * z) :=
  comm_tailO (commuteO_12_7 x y) z
theorem endO_12_7 (x y : K) : xd 12 x * xd 7 y = xd 7 y * xd 12 x :=
  (commuteO_12_7 x y).eq

theorem tailO_13_2 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 2 y * z) = xd 2 y * (xd 13 x * z) :=
  comm_tailO (commuteO_13_2 x y) z
theorem endO_13_2 (x y : K) : xd 13 x * xd 2 y = xd 2 y * xd 13 x :=
  (commuteO_13_2 x y).eq

theorem tailO_13_0 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 0 y * z) = xd 0 y * (xd 13 x * z) :=
  comm_tailO (commuteO_13_0 x y) z
theorem endO_13_0 (x y : K) : xd 13 x * xd 0 y = xd 0 y * xd 13 x :=
  (commuteO_13_0 x y).eq

theorem tailO_13_3 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 3 y * z) = xd 3 y * (xd 13 x * z) :=
  comm_tailO (commuteO_13_3 x y) z
theorem endO_13_3 (x y : K) : xd 13 x * xd 3 y = xd 3 y * xd 13 x :=
  (commuteO_13_3 x y).eq

theorem tailO_13_5 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 5 y * z) = xd 5 y * (xd 13 x * z) :=
  comm_tailO (commuteO_13_5 x y) z
theorem endO_13_5 (x y : K) : xd 13 x * xd 5 y = xd 5 y * xd 13 x :=
  (commuteO_13_5 x y).eq

theorem tailO_13_9 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 9 y * z) = xd 9 y * (xd 13 x * z) :=
  comm_tailO (commuteO_13_9 x y) z
theorem endO_13_9 (x y : K) : xd 13 x * xd 9 y = xd 9 y * xd 13 x :=
  (commuteO_13_9 x y).eq

theorem tailO_13_12 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 12 y * z) = xd 12 y * (xd 13 x * z) :=
  comm_tailO (commuteO_13_12 x y) z
theorem endO_13_12 (x y : K) : xd 13 x * xd 12 y = xd 12 y * xd 13 x :=
  (commuteO_13_12 x y).eq

theorem tailO_15_2 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 2 y * z) = xd 2 y * (xd 15 x * z) :=
  comm_tailO (commuteO_15_2 x y) z
theorem endO_15_2 (x y : K) : xd 15 x * xd 2 y = xd 2 y * xd 15 x :=
  (commuteO_15_2 x y).eq

theorem tailO_15_1 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 1 y * z) = xd 1 y * (xd 15 x * z) :=
  comm_tailO (commuteO_15_1 x y) z
theorem endO_15_1 (x y : K) : xd 15 x * xd 1 y = xd 1 y * xd 15 x :=
  (commuteO_15_1 x y).eq

theorem tailO_15_3 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 3 y * z) = xd 3 y * (xd 15 x * z) :=
  comm_tailO (commuteO_15_3 x y) z
theorem endO_15_3 (x y : K) : xd 15 x * xd 3 y = xd 3 y * xd 15 x :=
  (commuteO_15_3 x y).eq

theorem tailO_15_7 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 7 y * z) = xd 7 y * (xd 15 x * z) :=
  comm_tailO (commuteO_15_7 x y) z
theorem endO_15_7 (x y : K) : xd 15 x * xd 7 y = xd 7 y * xd 15 x :=
  (commuteO_15_7 x y).eq

theorem tailO_15_9 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 9 y * z) = xd 9 y * (xd 15 x * z) :=
  comm_tailO (commuteO_15_9 x y) z
theorem endO_15_9 (x y : K) : xd 15 x * xd 9 y = xd 9 y * xd 15 x :=
  (commuteO_15_9 x y).eq

theorem tailO_15_12 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 12 y * z) = xd 12 y * (xd 15 x * z) :=
  comm_tailO (commuteO_15_12 x y) z
theorem endO_15_12 (x y : K) : xd 15 x * xd 12 y = xd 12 y * xd 15 x :=
  (commuteO_15_12 x y).eq

theorem tailO_15_13 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 13 y * z) = xd 13 y * (xd 15 x * z) :=
  comm_tailO (commuteO_15_13 x y) z
theorem endO_15_13 (x y : K) : xd 15 x * xd 13 y = xd 13 y * xd 15 x :=
  (commuteO_15_13 x y).eq

theorem tailO_19_0 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 0 y * z) = xd 0 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_0 x y) z
theorem endO_19_0 (x y : K) : xd 19 x * xd 0 y = xd 0 y * xd 19 x :=
  (commuteO_19_0 x y).eq

theorem tailO_19_1 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 1 y * z) = xd 1 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_1 x y) z
theorem endO_19_1 (x y : K) : xd 19 x * xd 1 y = xd 1 y * xd 19 x :=
  (commuteO_19_1 x y).eq

theorem tailO_19_3 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 3 y * z) = xd 3 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_3 x y) z
theorem endO_19_3 (x y : K) : xd 19 x * xd 3 y = xd 3 y * xd 19 x :=
  (commuteO_19_3 x y).eq

theorem tailO_19_5 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 5 y * z) = xd 5 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_5 x y) z
theorem endO_19_5 (x y : K) : xd 19 x * xd 5 y = xd 5 y * xd 19 x :=
  (commuteO_19_5 x y).eq

theorem tailO_19_7 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 7 y * z) = xd 7 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_7 x y) z
theorem endO_19_7 (x y : K) : xd 19 x * xd 7 y = xd 7 y * xd 19 x :=
  (commuteO_19_7 x y).eq

theorem tailO_19_9 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 9 y * z) = xd 9 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_9 x y) z
theorem endO_19_9 (x y : K) : xd 19 x * xd 9 y = xd 9 y * xd 19 x :=
  (commuteO_19_9 x y).eq

theorem tailO_19_12 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 12 y * z) = xd 12 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_12 x y) z
theorem endO_19_12 (x y : K) : xd 19 x * xd 12 y = xd 12 y * xd 19 x :=
  (commuteO_19_12 x y).eq

theorem tailO_19_13 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 13 y * z) = xd 13 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_13 x y) z
theorem endO_19_13 (x y : K) : xd 19 x * xd 13 y = xd 13 y * xd 19 x :=
  (commuteO_19_13 x y).eq

theorem tailO_19_15 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 15 y * z) = xd 15 y * (xd 19 x * z) :=
  comm_tailO (commuteO_19_15 x y) z
theorem endO_19_15 (x y : K) : xd 19 x * xd 15 y = xd 15 y * xd 19 x :=
  (commuteO_19_15 x y).eq

theorem tailO_22_2 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 2 y * z) = xd 2 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_2 x y) z
theorem endO_22_2 (x y : K) : xd 22 x * xd 2 y = xd 2 y * xd 22 x :=
  (commuteO_22_2 x y).eq

theorem tailO_22_0 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 0 y * z) = xd 0 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_0 x y) z
theorem endO_22_0 (x y : K) : xd 22 x * xd 0 y = xd 0 y * xd 22 x :=
  (commuteO_22_0 x y).eq

theorem tailO_22_1 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 1 y * z) = xd 1 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_1 x y) z
theorem endO_22_1 (x y : K) : xd 22 x * xd 1 y = xd 1 y * xd 22 x :=
  (commuteO_22_1 x y).eq

theorem tailO_22_3 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 3 y * z) = xd 3 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_3 x y) z
theorem endO_22_3 (x y : K) : xd 22 x * xd 3 y = xd 3 y * xd 22 x :=
  (commuteO_22_3 x y).eq

theorem tailO_22_5 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 5 y * z) = xd 5 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_5 x y) z
theorem endO_22_5 (x y : K) : xd 22 x * xd 5 y = xd 5 y * xd 22 x :=
  (commuteO_22_5 x y).eq

theorem tailO_22_7 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 7 y * z) = xd 7 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_7 x y) z
theorem endO_22_7 (x y : K) : xd 22 x * xd 7 y = xd 7 y * xd 22 x :=
  (commuteO_22_7 x y).eq

theorem tailO_22_9 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 9 y * z) = xd 9 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_9 x y) z
theorem endO_22_9 (x y : K) : xd 22 x * xd 9 y = xd 9 y * xd 22 x :=
  (commuteO_22_9 x y).eq

theorem tailO_22_12 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 12 y * z) = xd 12 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_12 x y) z
theorem endO_22_12 (x y : K) : xd 22 x * xd 12 y = xd 12 y * xd 22 x :=
  (commuteO_22_12 x y).eq

theorem tailO_22_13 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 13 y * z) = xd 13 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_13 x y) z
theorem endO_22_13 (x y : K) : xd 22 x * xd 13 y = xd 13 y * xd 22 x :=
  (commuteO_22_13 x y).eq

theorem tailO_22_15 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 15 y * z) = xd 15 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_15 x y) z
theorem endO_22_15 (x y : K) : xd 22 x * xd 15 y = xd 15 y * xd 22 x :=
  (commuteO_22_15 x y).eq

theorem tailO_22_19 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 19 y * z) = xd 19 y * (xd 22 x * z) :=
  comm_tailO (commuteO_22_19 x y) z
theorem endO_22_19 (x y : K) : xd 22 x * xd 19 y = xd 19 y * xd 22 x :=
  (commuteO_22_19 x y).eq

theorem tailO_0_2 (x y : K) (z : adjointGroup d4 K) :
    xd 0 y * (xd 2 x * z) = xd 5 (-(x * y)) * (xd 2 x * (xd 0 y * z)) :=
  swap_tailO (swapO_0_2 x y) z
theorem endO_0_2 (x y : K) :
    xd 0 y * xd 2 x = xd 5 (-(x * y)) * (xd 2 x * xd 0 y) :=
  swapO_0_2 x y

theorem tailO_1_2 (x y : K) (z : adjointGroup d4 K) :
    xd 1 y * (xd 2 x * z) = xd 7 (-(x * y)) * (xd 2 x * (xd 1 y * z)) :=
  swap_tailO (swapO_1_2 x y) z
theorem endO_1_2 (x y : K) :
    xd 1 y * xd 2 x = xd 7 (-(x * y)) * (xd 2 x * xd 1 y) :=
  swapO_1_2 x y

theorem tailO_3_2 (x y : K) (z : adjointGroup d4 K) :
    xd 3 y * (xd 2 x * z) = xd 9 (x * y) * (xd 2 x * (xd 3 y * z)) :=
  swap_tailO (swapO_3_2 x y) z
theorem endO_3_2 (x y : K) :
    xd 3 y * xd 2 x = xd 9 (x * y) * (xd 2 x * xd 3 y) :=
  swapO_3_2 x y

theorem tailO_5_1 (x y : K) (z : adjointGroup d4 K) :
    xd 5 y * (xd 1 x * z) = xd 12 (-(x * y)) * (xd 1 x * (xd 5 y * z)) :=
  swap_tailO (swapO_5_1 x y) z
theorem endO_5_1 (x y : K) :
    xd 5 y * xd 1 x = xd 12 (-(x * y)) * (xd 1 x * xd 5 y) :=
  swapO_5_1 x y

theorem tailO_5_3 (x y : K) (z : adjointGroup d4 K) :
    xd 5 y * (xd 3 x * z) = xd 13 (-(x * y)) * (xd 3 x * (xd 5 y * z)) :=
  swap_tailO (swapO_5_3 x y) z
theorem endO_5_3 (x y : K) :
    xd 5 y * xd 3 x = xd 13 (-(x * y)) * (xd 3 x * xd 5 y) :=
  swapO_5_3 x y

theorem tailO_7_0 (x y : K) (z : adjointGroup d4 K) :
    xd 7 y * (xd 0 x * z) = xd 12 (-(x * y)) * (xd 0 x * (xd 7 y * z)) :=
  swap_tailO (swapO_7_0 x y) z
theorem endO_7_0 (x y : K) :
    xd 7 y * xd 0 x = xd 12 (-(x * y)) * (xd 0 x * xd 7 y) :=
  swapO_7_0 x y

theorem tailO_7_3 (x y : K) (z : adjointGroup d4 K) :
    xd 7 y * (xd 3 x * z) = xd 15 (-(x * y)) * (xd 3 x * (xd 7 y * z)) :=
  swap_tailO (swapO_7_3 x y) z
theorem endO_7_3 (x y : K) :
    xd 7 y * xd 3 x = xd 15 (-(x * y)) * (xd 3 x * xd 7 y) :=
  swapO_7_3 x y

theorem tailO_9_0 (x y : K) (z : adjointGroup d4 K) :
    xd 9 y * (xd 0 x * z) = xd 13 (x * y) * (xd 0 x * (xd 9 y * z)) :=
  swap_tailO (swapO_9_0 x y) z
theorem endO_9_0 (x y : K) :
    xd 9 y * xd 0 x = xd 13 (x * y) * (xd 0 x * xd 9 y) :=
  swapO_9_0 x y

theorem tailO_9_1 (x y : K) (z : adjointGroup d4 K) :
    xd 9 y * (xd 1 x * z) = xd 15 (x * y) * (xd 1 x * (xd 9 y * z)) :=
  swap_tailO (swapO_9_1 x y) z
theorem endO_9_1 (x y : K) :
    xd 9 y * xd 1 x = xd 15 (x * y) * (xd 1 x * xd 9 y) :=
  swapO_9_1 x y

theorem tailO_12_3 (x y : K) (z : adjointGroup d4 K) :
    xd 12 y * (xd 3 x * z) = xd 19 (-(x * y)) * (xd 3 x * (xd 12 y * z)) :=
  swap_tailO (swapO_12_3 x y) z
theorem endO_12_3 (x y : K) :
    xd 12 y * xd 3 x = xd 19 (-(x * y)) * (xd 3 x * xd 12 y) :=
  swapO_12_3 x y

theorem tailO_12_9 (x y : K) (z : adjointGroup d4 K) :
    xd 12 y * (xd 9 x * z) = xd 22 (x * y) * (xd 9 x * (xd 12 y * z)) :=
  swap_tailO (swapO_12_9 x y) z
theorem endO_12_9 (x y : K) :
    xd 12 y * xd 9 x = xd 22 (x * y) * (xd 9 x * xd 12 y) :=
  swapO_12_9 x y

theorem tailO_13_1 (x y : K) (z : adjointGroup d4 K) :
    xd 13 y * (xd 1 x * z) = xd 19 (-(x * y)) * (xd 1 x * (xd 13 y * z)) :=
  swap_tailO (swapO_13_1 x y) z
theorem endO_13_1 (x y : K) :
    xd 13 y * xd 1 x = xd 19 (-(x * y)) * (xd 1 x * xd 13 y) :=
  swapO_13_1 x y

theorem tailO_13_7 (x y : K) (z : adjointGroup d4 K) :
    xd 13 y * (xd 7 x * z) = xd 22 (-(x * y)) * (xd 7 x * (xd 13 y * z)) :=
  swap_tailO (swapO_13_7 x y) z
theorem endO_13_7 (x y : K) :
    xd 13 y * xd 7 x = xd 22 (-(x * y)) * (xd 7 x * xd 13 y) :=
  swapO_13_7 x y

theorem tailO_15_0 (x y : K) (z : adjointGroup d4 K) :
    xd 15 y * (xd 0 x * z) = xd 19 (-(x * y)) * (xd 0 x * (xd 15 y * z)) :=
  swap_tailO (swapO_15_0 x y) z
theorem endO_15_0 (x y : K) :
    xd 15 y * xd 0 x = xd 19 (-(x * y)) * (xd 0 x * xd 15 y) :=
  swapO_15_0 x y

theorem tailO_15_5 (x y : K) (z : adjointGroup d4 K) :
    xd 15 y * (xd 5 x * z) = xd 22 (-(x * y)) * (xd 5 x * (xd 15 y * z)) :=
  swap_tailO (swapO_15_5 x y) z
theorem endO_15_5 (x y : K) :
    xd 15 y * xd 5 x = xd 22 (-(x * y)) * (xd 5 x * xd 15 y) :=
  swapO_15_5 x y

theorem tailO_19_2 (x y : K) (z : adjointGroup d4 K) :
    xd 19 y * (xd 2 x * z) = xd 22 (-(x * y)) * (xd 2 x * (xd 19 y * z)) :=
  swap_tailO (swapO_19_2 x y) z
theorem endO_19_2 (x y : K) :
    xd 19 y * xd 2 x = xd 22 (-(x * y)) * (xd 2 x * xd 19 y) :=
  swapO_19_2 x y

end Collection

macro "d4collO" : tactic => `(tactic| simp only [mul_assoc, tailO_1_0, endO_1_0, tailO_3_0, endO_3_0, tailO_3_1, endO_3_1, tailO_5_2, endO_5_2, tailO_5_0, endO_5_0, tailO_7_2, endO_7_2, tailO_7_1, endO_7_1, tailO_7_5, endO_7_5, tailO_9_2, endO_9_2, tailO_9_3, endO_9_3, tailO_9_5, endO_9_5, tailO_9_7, endO_9_7, tailO_12_2, endO_12_2, tailO_12_0, endO_12_0, tailO_12_1, endO_12_1, tailO_12_5, endO_12_5, tailO_12_7, endO_12_7, tailO_13_2, endO_13_2, tailO_13_0, endO_13_0, tailO_13_3, endO_13_3, tailO_13_5, endO_13_5, tailO_13_9, endO_13_9, tailO_13_12, endO_13_12, tailO_15_2, endO_15_2, tailO_15_1, endO_15_1, tailO_15_3, endO_15_3, tailO_15_7, endO_15_7, tailO_15_9, endO_15_9, tailO_15_12, endO_15_12, tailO_15_13, endO_15_13, tailO_19_0, endO_19_0, tailO_19_1, endO_19_1, tailO_19_3, endO_19_3, tailO_19_5, endO_19_5, tailO_19_7, endO_19_7, tailO_19_9, endO_19_9, tailO_19_12, endO_19_12, tailO_19_13, endO_19_13, tailO_19_15, endO_19_15, tailO_22_2, endO_22_2, tailO_22_0, endO_22_0, tailO_22_1, endO_22_1, tailO_22_3, endO_22_3, tailO_22_5, endO_22_5, tailO_22_7, endO_22_7, tailO_22_9, endO_22_9, tailO_22_12, endO_22_12, tailO_22_13, endO_22_13, tailO_22_15, endO_22_15, tailO_22_19, endO_22_19, tailO_0_2, endO_0_2, tailO_1_2, endO_1_2, tailO_3_2, endO_3_2, tailO_5_1, endO_5_1, tailO_5_3, endO_5_3, tailO_7_0, endO_7_0, tailO_7_3, endO_7_3, tailO_9_0, endO_9_0, tailO_9_1, endO_9_1, tailO_12_3, endO_12_3, tailO_12_9, endO_12_9, tailO_13_1, endO_13_1, tailO_13_7, endO_13_7, tailO_15_0, endO_15_0, tailO_15_5, endO_15_5, tailO_19_2, endO_19_2,
    xd_mergeO, xd_mergeO', xd_inv_odd, mul_inv_rev, add_neg_cancel, neg_add_cancel, xd_zero, one_mul, mul_one])

macro "d4finO" : tactic => `(tactic| (ring_nf; try simp [xd_zero]; try ring_nf))

theorem conj_xA_xB_odd (σ : K →+* K) (a d : K) :
    (xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a))) * xd 2 d * (xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)))⁻¹ =
      xd 2 d * (xd 5 (-(a * d)) * xd 7 (-(σ a * d)) * xd 9 (σ (σ a) * d)) *
        (xd 12 (-(a * σ a * d)) * xd 15 (-(σ a * σ (σ a) * d)) * xd 13 (-(a * σ (σ a) * d))) *
        xd 19 (-(a * σ a * σ (σ a) * d)) * xd 22 (-(a * σ a * σ (σ a) * d ^ 2)) := by
  d4collO
  d4finO

end CFSG.HardMathSupport.Seitz.TrialityOdd
