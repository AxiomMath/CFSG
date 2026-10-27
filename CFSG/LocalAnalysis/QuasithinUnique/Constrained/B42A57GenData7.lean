module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57GenCore
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.B42A57

open Equiv Equiv.Perm

set_option maxRecDepth 100000

@[expose] def inv7_0 : GenEntry 7 where
  T := [swap 4 5]
  Tt := [[0, 1, 2, 3, 5, 4, 6]]
  cs := [[(0, 4), (4, 1), (1, 5), (5, 2), (2, 6), (6, 3)], [(1, 2), (2, 6), (3, 5), (5, 4)], [(0, 6), (6, 3), (3, 2), (2, 1)], [(0, 2), (1, 4), (4, 6), (3, 5)], [(0, 4), (4, 3), (3, 1), (1, 6), (6, 2), (2, 5)], [(0, 5), (5, 1), (1, 3), (2, 6)]]
  ws := [[4, 1, 5, 0, 1, 4], [1, 5, 1, 4], [4, 5, 1, 4], [2, 4, 5, 1, 2, 4], [3, 1, 5, 1, 4, 3]]

theorem inv7_0_ok : inv7_0.Ok := by decide +kernel

@[expose] def inv7_1 : GenEntry 7 where
  T := [swap 1 3]
  Tt := [[0, 3, 2, 1, 4, 5, 6]]
  cs := [[(0, 5), (1, 4), (4, 2), (3, 6)], [(0, 2), (2, 5), (5, 4), (4, 6), (6, 1), (1, 3)], [(0, 6), (6, 3), (3, 2), (1, 5)], [(0, 2), (1, 4), (4, 6), (3, 5)], [(0, 3), (3, 2), (2, 5), (4, 6)], [(0, 5), (5, 1), (1, 3), (3, 4), (4, 6), (6, 2)]]
  ws := [[1, 4, 2, 3, 5, 1, 3, 2], [4, 2, 3, 5, 1, 3, 2, 4], [1, 3, 2, 4, 2, 3, 5, 1], [1, 2, 4, 2, 3, 5, 1, 3], [0, 1, 3, 2, 4, 2, 3, 5, 0, 1]]

theorem inv7_1_ok : inv7_1.Ok := by decide +kernel

@[expose] def inv7_2 : GenEntry 7 where
  T := [swap 1 3 * swap 4 5]
  Tt := [[0, 3, 2, 1, 5, 4, 6]]
  cs := [[(0, 2), (2, 3), (3, 5), (5, 4), (4, 6), (6, 1)], [(0, 5), (1, 2), (2, 6), (6, 4)], [(1, 3), (3, 4), (4, 5), (5, 2)]]
  ws := [[2, 1, 0, 1, 0, 2], [1, 2, 0, 1, 0, 1, 2, 1], [2, 1, 2, 0, 1, 0, 1, 2, 1, 2], [1, 0, 1, 0], [0, 1, 2, 1, 2, 0, 1]]

theorem inv7_2_ok : inv7_2.Ok := by decide +kernel

@[expose] def inv7_3 : GenEntry 7 where
  T := [swap 0 1 * swap 2 3]
  Tt := [[1, 0, 3, 2, 4, 5, 6]]
  cs := [[(1, 2), (2, 5), (5, 6), (6, 3)], [(0, 3), (1, 4), (2, 5), (5, 6)], [(1, 3), (3, 6), (6, 2), (2, 4)]]
  ws := [[2, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 2], [1, 0, 1, 2, 1, 0, 1, 2], [0, 1, 2, 0, 2, 0, 1, 0], [2, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 2], [0, 2, 1, 2, 0, 2, 0, 1, 2, 0]]

theorem inv7_3_ok : inv7_3.Ok := by decide +kernel

@[expose] def inv7_4 : GenEntry 7 where
  T := [swap 0 1 * swap 2 3 * swap 4 5]
  Tt := [[1, 0, 3, 2, 5, 4, 6]]
  cs := [[(0, 3), (3, 5), (5, 6), (6, 2)], [(0, 6), (6, 1), (1, 2), (2, 5)], [(0, 4), (4, 3), (3, 6), (6, 1), (1, 2), (2, 5)]]
  ws := [[2, 0, 2, 1, 0, 1, 2, 1], [2, 0, 1, 0], [2, 0, 1, 2, 1, 0, 2, 1], [2, 0, 1, 2, 0, 1], [2, 0, 2, 0, 1, 2]]

theorem inv7_4_ok : inv7_4.Ok := by decide +kernel

@[expose] def inv7_5 : GenEntry 7 where
  T := [swap 0 2]
  Tt := [[2, 1, 0, 3, 4, 5, 6]]
  cs := [[(0, 1), (1, 5), (5, 3), (4, 6)], [(0, 6), (6, 4), (1, 3), (2, 5)], [(1, 3), (2, 4), (4, 6), (6, 5)], [(0, 2), (2, 6), (6, 4), (4, 5), (5, 3), (3, 1)], [(1, 2), (2, 6), (6, 4), (4, 5)], [(0, 3), (1, 6), (6, 4), (4, 2)]]
  ws := [[0, 3, 4, 3], [0, 3, 4, 3, 0, 5], [0, 2, 3, 4, 3, 0], [0, 1, 3, 0, 4, 1], [0, 3, 0, 4]]

theorem inv7_5_ok : inv7_5.Ok := by decide +kernel

@[expose] def inv7_6 : GenEntry 7 where
  T := [swap 0 2 * swap 4 5]
  Tt := [[2, 1, 0, 3, 5, 4, 6]]
  cs := [[(1, 6), (2, 5)], [(0, 4), (4, 5), (5, 2), (2, 3)], [(1, 5), (2, 6), (6, 3), (3, 4)]]
  ws := [[2, 1, 2, 1, 0, 1, 0, 2, 1, 2, 0, 1, 0], [1, 0, 1, 2, 1, 2, 0, 1], [0, 1, 2, 1, 2, 0], [2, 0, 1, 2, 0, 1, 0, 1, 0, 2, 1, 0, 1, 2], [2, 0, 1, 0, 2, 1, 2, 0, 1, 0, 1, 2, 1, 2]]

theorem inv7_6_ok : inv7_6.Ok := by decide +kernel

@[expose] def inv7_7 : GenEntry 7 where
  T := [swap 0 2 * swap 1 3]
  Tt := [[2, 3, 0, 1, 4, 5, 6]]
  cs := [[(0, 2), (2, 3), (3, 4), (1, 5)], [(0, 6), (6, 5), (5, 4), (4, 2), (2, 3), (3, 1)], [(0, 2), (2, 1), (1, 4), (4, 6), (6, 5), (5, 3)]]
  ws := [[0, 1, 2, 0, 1, 0, 1, 2, 0], [1, 2, 0, 1, 0, 1, 2], [0, 2, 0, 1, 0, 1, 0, 2, 1, 0], [2, 0, 1, 0, 1, 0, 2, 1], [1, 2, 1, 0, 1, 0, 2]]

theorem inv7_7_ok : inv7_7.Ok := by decide +kernel

@[expose] def inv7_8 : GenEntry 7 where
  T := [swap 0 2 * swap 1 3 * swap 4 5]
  Tt := [[2, 3, 0, 1, 5, 4, 6]]
  cs := [[(0, 1), (1, 2), (3, 6), (6, 5)], [(0, 2), (1, 3), (4, 5), (5, 6)], [(0, 4), (4, 1)]]
  ws := [[0, 2, 1, 0, 2, 0, 2, 1], [1, 0, 2, 1, 0, 1, 0, 2, 0, 2, 0, 1], [1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 2, 1], [0, 1, 0, 2, 0, 1], [0, 1, 2, 0, 2, 0, 1, 2]]

theorem inv7_8_ok : inv7_8.Ok := by decide +kernel

@[expose] def inv7_9 : GenEntry 7 where
  T := [swap 0 3 * swap 1 2]
  Tt := [[3, 2, 1, 0, 4, 5, 6]]
  cs := [[(0, 4), (4, 2), (1, 6), (6, 5)], [(0, 4), (4, 3), (3, 5), (5, 6)], [(1, 6), (6, 5), (5, 4), (2, 3)]]
  ws := [[2, 1, 2, 1], [2, 0, 1, 2, 1, 2, 0, 2], [0, 1, 2, 0, 1, 2, 1, 2, 1, 0, 1], [1, 0, 2, 1, 0, 2, 1, 2, 0], [0, 1, 0, 1, 0, 2, 1, 2]]

theorem inv7_9_ok : inv7_9.Ok := by decide +kernel

@[expose] def inv7_10 : GenEntry 7 where
  T := [swap 0 3 * swap 1 2 * swap 4 5]
  Tt := [[3, 2, 1, 0, 5, 4, 6]]
  cs := [[(1, 5), (5, 4), (4, 3), (3, 2)], [(0, 2), (2, 4), (4, 3), (3, 5)], [(0, 1), (2, 3), (4, 5), (5, 6)]]
  ws := [[0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0], [1, 2, 1, 2, 1, 0, 2, 0, 1, 2], [2, 0, 2, 0, 1, 0, 2, 1, 0, 2, 1, 0], [0, 2, 0, 1, 2, 0, 2, 0, 1, 2], [0, 1, 2, 0, 2, 1, 2, 0, 2, 0]]

theorem inv7_10_ok : inv7_10.Ok := by decide +kernel

@[expose] def pair7_0 : GenEntry 7 where
  T := [swap 0 1 * swap 2 3, swap 0 1 * swap 2 3 * swap 4 5]
  Tt := [[1, 0, 3, 2, 4, 5, 6], [1, 0, 3, 2, 5, 4, 6]]
  cs := [[(0, 2), (2, 3), (1, 6), (4, 5)], [(0, 4), (4, 5), (5, 1), (2, 3)]]
  ws := [[2, 1, 2, 0, 1, 3, 1, 2], [3, 0, 1, 2, 0, 2, 0, 1, 3, 0], [0, 1, 3, 0, 1, 2, 0, 1], [3, 0, 1, 2], [3, 1, 2, 0, 2, 1, 2, 0, 3, 0]]

theorem pair7_0_ok : pair7_0.Ok := by decide +kernel

@[expose] def pair7_1 : GenEntry 7 where
  T := [swap 0 2 * swap 1 3, swap 0 2 * swap 1 3 * swap 4 5]
  Tt := [[2, 3, 0, 1, 4, 5, 6], [2, 3, 0, 1, 5, 4, 6]]
  cs := [[(0, 1), (1, 2), (2, 5), (5, 6), (6, 4), (4, 3)], [(1, 2), (2, 5), (5, 3), (3, 4)]]
  ws := [[3, 0, 3, 0, 2, 0, 3, 0, 2, 0, 2, 3], [3, 0, 2, 3, 0, 2], [3, 0, 3, 0, 2, 3, 0, 2, 0, 3], [3, 0, 2, 3, 0, 2, 0, 2, 3, 0, 2, 3], [3, 0, 2, 3, 1, 3]]

theorem pair7_1_ok : pair7_1.Ok := by decide +kernel

@[expose] def pair7_2 : GenEntry 7 where
  T := [swap 0 3 * swap 1 2, swap 0 3 * swap 1 2 * swap 4 5]
  Tt := [[3, 2, 1, 0, 4, 5, 6], [3, 2, 1, 0, 5, 4, 6]]
  cs := [[(0, 3), (3, 1), (1, 6), (6, 2), (2, 5), (5, 4)], [(0, 6), (1, 4), (4, 2), (2, 3)]]
  ws := [[0, 2, 1, 2, 0, 2, 0, 3, 0, 2], [2, 0, 1, 2, 0, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0], [0, 2, 0, 2, 0, 1, 2, 1, 2, 0], [2, 0, 2, 1, 2, 0, 2, 1, 2, 0]]

theorem pair7_2_ok : pair7_2.Ok := by decide +kernel

@[expose] def pair7_3 : GenEntry 7 where
  T := [swap 0 2 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5]
  Tt := [[2, 1, 0, 3, 5, 4, 6], [2, 3, 0, 1, 5, 4, 6]]
  cs := [[(0, 3), (3, 6), (6, 4), (1, 2)], [(2, 4), (4, 5), (5, 3), (3, 6)]]
  ws := [[0, 1, 2, 3, 0, 2, 0, 2, 3, 0, 2, 1], [2, 3, 0, 2, 0, 2, 3, 0, 3, 0, 2, 3], [2, 3, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3], [2, 3, 0, 2, 0, 3, 0, 2, 0, 3, 0, 3], [2, 3, 0, 2, 0, 2, 3, 0, 2, 0]]

theorem pair7_3_ok : pair7_3.Ok := by decide +kernel

@[expose] def pair7_4 : GenEntry 7 where
  T := [swap 1 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5]
  Tt := [[0, 3, 2, 1, 5, 4, 6], [2, 3, 0, 1, 5, 4, 6]]
  cs := [[(0, 5), (5, 4), (4, 6), (1, 3)], [(1, 6), (6, 4), (4, 2), (3, 5)]]
  ws := [[0, 2, 0, 3, 0, 3], [0, 2, 3, 0, 2, 3], [3, 0, 2, 1, 2, 0], [1, 2, 0, 3, 0, 3, 0, 1], [2, 0, 1, 2, 0, 3, 0, 2, 1, 3]]

theorem pair7_4_ok : pair7_4.Ok := by decide +kernel

@[expose] def pair7_5 : GenEntry 7 where
  T := [swap 1 3 * swap 4 5, swap 0 2 * swap 4 5]
  Tt := [[0, 3, 2, 1, 5, 4, 6], [2, 1, 0, 3, 5, 4, 6]]
  cs := [[(1, 6), (6, 4), (4, 5), (5, 2)], [(0, 1), (1, 6), (6, 5), (5, 2), (2, 3), (3, 4)]]
  ws := [[3, 1, 2, 3, 1, 2, 3], [2, 3, 1, 2, 3, 1], [1, 2, 0, 3, 0, 2], [2, 1, 3, 1, 2, 3, 1, 3], [0, 2, 3, 1, 2, 3, 0, 1]]

theorem pair7_5_ok : pair7_5.Ok := by decide +kernel

@[expose] def pair7_6 : GenEntry 7 where
  T := [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3]
  Tt := [[1, 0, 3, 2, 4, 5, 6], [2, 3, 0, 1, 4, 5, 6]]
  cs := [[(0, 5), (1, 4), (2, 3), (3, 6)], [(0, 1), (3, 6)]]
  ws := [[0, 2, 0, 2, 3, 0, 3, 0, 2], [2, 3, 0, 2, 0, 3], [2, 3, 1, 2, 1, 3], [0, 2, 3, 1, 2, 1, 3, 0], [0, 2, 3, 0, 2, 0, 3, 0]]

theorem pair7_6_ok : pair7_6.Ok := by decide +kernel

@[expose] def pair7_7 : GenEntry 7 where
  T := [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3 * swap 4 5]
  Tt := [[1, 0, 3, 2, 4, 5, 6], [2, 3, 0, 1, 5, 4, 6]]
  cs := [[(0, 2), (3, 6), (6, 4), (4, 5)], [(0, 5), (5, 2), (2, 1), (1, 6), (6, 3), (3, 4)]]
  ws := [[3, 0, 1, 3, 1, 2, 0, 1, 3], [0, 3, 0, 1, 2, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2, 1, 2, 0, 1, 3, 1], [0, 3, 0, 1, 2, 1, 3, 0, 1, 3]]

theorem pair7_7_ok : pair7_7.Ok := by decide +kernel

@[expose] def pair7_8 : GenEntry 7 where
  T := [swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3]
  Tt := [[1, 0, 3, 2, 5, 4, 6], [2, 3, 0, 1, 4, 5, 6]]
  cs := [[(0, 4), (4, 5), (5, 6), (6, 2), (2, 1), (1, 3)], [(0, 5), (5, 6), (1, 3), (2, 4)]]
  ws := [[0, 1, 3, 0, 2, 0, 3, 1], [1, 3, 1, 2, 1, 2, 3], [2, 3, 1, 2, 1, 3], [1, 2, 1, 2, 3, 1, 3], [0, 3, 1, 2, 3, 1, 2, 0, 1]]

theorem pair7_8_ok : pair7_8.Ok := by decide +kernel

@[expose] def pair7_9 : GenEntry 7 where
  T := [swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5]
  Tt := [[1, 0, 3, 2, 5, 4, 6], [2, 3, 0, 1, 5, 4, 6]]
  cs := [[(0, 1), (1, 2), (2, 4), (4, 5)], [(0, 4), (4, 6), (6, 2), (1, 5)]]
  ws := [[2, 1, 2, 0, 3, 1, 3, 0], [1, 2, 0, 1, 3, 1, 3, 1, 3, 0], [0, 1, 2, 1, 3, 1, 2, 1, 3, 0], [2, 0, 1, 2, 0, 2, 1, 2], [3, 1, 3, 1, 2, 0, 2, 0, 2, 1]]

theorem pair7_9_ok : pair7_9.Ok := by decide +kernel

@[expose] def table7 : List (GenEntry 7) :=
  [inv7_0, inv7_1, inv7_2, inv7_3, inv7_4, inv7_5, inv7_6, inv7_7, inv7_8, inv7_9, inv7_10]

theorem table7_ok : ∀ e ∈ table7, e.Ok := by
  intro e he
  simp only [table7, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [inv7_0_ok, inv7_1_ok, inv7_2_ok, inv7_3_ok, inv7_4_ok, inv7_5_ok, inv7_6_ok, inv7_7_ok,
    inv7_8_ok, inv7_9_ok, inv7_10_ok]

@[expose] def pairs7 : List (GenEntry 7) :=
  [pair7_0, pair7_1, pair7_2, pair7_3, pair7_4, pair7_5, pair7_6, pair7_7, pair7_8, pair7_9]

theorem pairs7_ok : ∀ e ∈ pairs7, e.Ok := by
  intro e he
  simp only [pairs7, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [pair7_0_ok, pair7_1_ok, pair7_2_ok, pair7_3_ok, pair7_4_ok, pair7_5_ok, pair7_6_ok,
    pair7_7_ok, pair7_8_ok, pair7_9_ok]

end CFSG.QuasithinUnique.B42A57
