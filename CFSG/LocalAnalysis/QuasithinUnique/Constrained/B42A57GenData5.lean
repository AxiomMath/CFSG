module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57GenCore
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.B42A57

open Equiv Equiv.Perm

set_option maxRecDepth 100000

@[expose] def inv5_0 : GenEntry 5 where
  T := [swap 1 3]
  Tt := [[0, 3, 2, 1, 4]]
  cs := [[(0, 4), (4, 3), (3, 2), (2, 1)], [(1, 2), (2, 3)], [(0, 1), (1, 2), (2, 3), (3, 4)], [(1, 3), (3, 4)]]
  ws := [[1, 0], [0, 2, 3, 2, 1, 0], [0, 2, 1, 0]]

theorem inv5_0_ok : inv5_0.Ok := by decide +kernel

@[expose] def inv5_1 : GenEntry 5 where
  T := [swap 0 1 * swap 2 3]
  Tt := [[1, 0, 3, 2, 4]]
  cs := [[(0, 3), (3, 1)], [(0, 4), (4, 3), (3, 1), (1, 2)], [(0, 1), (3, 4)], [(0, 4), (4, 2), (2, 1), (1, 3)]]
  ws := [[0, 1, 0, 1, 0, 3], [1, 0, 3, 0, 3, 0], [0, 1, 3, 0]]

theorem inv5_1_ok : inv5_1.Ok := by decide +kernel

@[expose] def inv5_2 : GenEntry 5 where
  T := [swap 0 2]
  Tt := [[2, 1, 0, 3, 4]]
  cs := [[(1, 4), (2, 3)], [(0, 3), (2, 4)], [(0, 4), (4, 3), (3, 2), (2, 1)], [(0, 2), (1, 3)]]
  ws := [[2, 1, 3, 0, 1, 2], [1, 2, 1, 0], [0, 2, 1, 0]]

theorem inv5_2_ok : inv5_2.Ok := by decide +kernel

@[expose] def inv5_3 : GenEntry 5 where
  T := [swap 0 2 * swap 1 3]
  Tt := [[2, 3, 0, 1, 4]]
  cs := [[(0, 2), (2, 3), (3, 4), (4, 1)], [(0, 3), (3, 4)], [(0, 4), (4, 2)], [(0, 4), (4, 2), (2, 1), (1, 3)]]
  ws := [[0, 2, 3, 1], [0, 1, 2], [1, 0]]

theorem inv5_3_ok : inv5_3.Ok := by decide +kernel

@[expose] def inv5_4 : GenEntry 5 where
  T := [swap 0 3 * swap 1 2]
  Tt := [[3, 2, 1, 0, 4]]
  cs := [[(0, 2), (2, 1), (1, 3), (3, 4)], [(1, 3), (3, 2)], [(0, 2), (3, 4)], [(0, 4), (4, 3)]]
  ws := [[1, 0, 2], [2, 0], [0, 1, 2]]

theorem inv5_4_ok : inv5_4.Ok := by decide +kernel

@[expose] def V_5 : GenEntry 5 where
  T := [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3]
  Tt := [[1, 0, 3, 2, 4], [2, 3, 0, 1, 4]]
  cs := [[(0, 3), (3, 1), (1, 2), (2, 4)], [(0, 2), (2, 4), (4, 3), (3, 1)]]
  ws := [[1, 3, 0, 3], [3, 0, 1], [0, 3, 1, 3]]

theorem V_5_ok : V_5.Ok := by decide +kernel

@[expose] def Vp_5 : GenEntry 5 where
  T := [swap 0 2, swap 1 3]
  Tt := [[2, 1, 0, 3, 4], [0, 3, 2, 1, 4]]
  cs := [[(0, 1), (1, 3), (3, 4), (4, 2)], [(0, 4), (4, 1), (1, 3), (3, 2)]]
  ws := [[2, 1, 3, 1, 2, 0], [1, 2, 0, 1], [2, 0]]

theorem Vp_5_ok : Vp_5.Ok := by decide +kernel

@[expose] def table5 : List (GenEntry 5) :=
  [inv5_0, inv5_1, inv5_2, inv5_3, inv5_4]

@[expose] def pairs5 : List (GenEntry 5) := [V_5, Vp_5]

theorem pairs5_ok : ∀ e ∈ pairs5, e.Ok := by
  intro e he
  simp only [pairs5, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  exacts [V_5_ok, Vp_5_ok]

theorem table5_ok : ∀ e ∈ table5, e.Ok := by
  intro e he
  simp only [table5, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  exacts [inv5_0_ok, inv5_1_ok, inv5_2_ok, inv5_3_ok, inv5_4_ok]

end CFSG.QuasithinUnique.B42A57
