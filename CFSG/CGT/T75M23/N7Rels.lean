module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable

@[expose] def rels7 : List (List (Fin 6 × Bool)) :=
  [[(0, true), (0, true)],
   [(1, true), (1, true), (1, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false)],
   [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
    (1, false), (0, true), (1, false), (0, true), (1, false), (0, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false)],
   [(2, true), (2, true)],
   [(3, true), (3, true)],
   [(4, true), (4, true)],
   [(5, true), (5, true)],
   [(2, true), (3, true), (2, true), (3, true)],
   [(2, true), (4, true), (2, true), (4, true)],
   [(2, true), (5, true), (2, true), (5, true)],
   [(3, true), (4, true), (3, true), (4, true)],
   [(3, true), (5, true), (3, true), (5, true)],
   [(4, true), (5, true), (4, true), (5, true)],
   [(0, true), (2, true), (0, false), (5, false), (2, false)],
   [(0, true), (3, true), (0, false), (5, false), (3, false)],
   [(0, true), (4, true), (0, false), (5, false), (4, false), (3, false), (2, false)],
   [(0, true), (5, true), (0, false), (5, false)],
   [(1, true), (2, true), (1, false), (3, false)],
   [(1, true), (3, true), (1, false), (4, false), (3, false)],
   [(1, true), (4, true), (1, false), (5, false), (3, false)],
   [(1, true), (5, true), (1, false), (3, false), (2, false)]]

abbrev rels7K := restrictWords (subsetOf 6 [0, 1]) rels7

@[expose] def n7Enum2 : Bool := subsetCheck rels7 [0, 1] 200000 16

@[expose] def n7Enum1 : Bool := subsetCheck rels7K [] 20000 2520

theorem rels7_card_le (h2 : n7Enum2 = true) (h1 : n7Enum1 = true) :
    Finite (PG 6 rels7) ∧ Nat.card (PG 6 rels7) ≤ 40320 := by
  have h2' : subsetCheck rels7 [0, 1] 200000 16 = true := h2
  have h1' : subsetCheck rels7K [] 20000 2520 = true := h1
  obtain ⟨f1, c1⟩ := card_le_of_subsetCheck_nil rels7K h1'
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheck rels7 [0, 1] h2'
  refine ⟨f2, ?_⟩
  have := c2.trans <| Nat.mul_le_mul_left _ c1
  exact this.trans (by norm_num)

end CFSG.CGT.T75M23
