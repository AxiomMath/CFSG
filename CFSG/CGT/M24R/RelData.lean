module

public import CFSG.CGT.M24R.Words

public section

namespace CFSG.CGT.M24R

@[expose] def carmRels : List M24Word :=
  [[(0, true), (0, true), (0, true)],
   [(0, true), (1, true), (0, true), (1, true)],
   [(0, true), (2, true), (0, true), (2, true)],
   [(0, true), (3, true), (0, true), (3, true)],
   [(0, true), (4, true), (0, true), (4, true)],
   [(0, true), (5, true), (0, true), (5, true)],
   [(1, true), (1, true), (1, true)],
   [(1, true), (2, true), (1, true), (2, true)],
   [(1, true), (3, true), (1, true), (3, true)],
   [(1, true), (4, true), (1, true), (4, true)],
   [(1, true), (5, true), (1, true), (5, true)],
   [(2, true), (2, true), (2, true)],
   [(2, true), (3, true), (2, true), (3, true)],
   [(2, true), (4, true), (2, true), (4, true)],
   [(2, true), (5, true), (2, true), (5, true)],
   [(3, true), (3, true), (3, true)],
   [(3, true), (4, true), (3, true), (4, true)],
   [(3, true), (5, true), (3, true), (5, true)],
   [(4, true), (4, true), (4, true)],
   [(4, true), (5, true), (4, true), (5, true)],
   [(5, true), (5, true), (5, true)]]

@[expose] def tRels : List M24Word :=
  [[(6, true), (6, true)],
   [(6, true), (7, true), (6, true), (7, true)],
   [(6, true), (8, true), (6, true), (8, true)],
   [(6, true), (9, true), (6, true), (9, true)],
   [(7, true), (7, true)],
   [(7, true), (8, true), (7, true), (8, true)],
   [(7, true), (9, true), (7, true), (9, true)],
   [(8, true), (8, true)],
   [(8, true), (9, true), (8, true), (9, true)],
   [(9, true), (9, true)]]

@[expose] def actRels : List M24Word :=
  [[(0, true), (6, true), (0, false), (9, false), (7, false)],
   [(0, true), (7, true), (0, false), (8, false), (7, false)],
   [(0, true), (8, true), (0, false), (7, false)],
   [(0, true), (9, true), (0, false), (9, false), (8, false), (6, false)],
   [(1, true), (6, true), (1, false), (9, false), (8, false), (7, false)],
   [(1, true), (7, true), (1, false), (9, false), (6, false)],
   [(1, true), (8, true), (1, false), (7, false), (6, false)],
   [(1, true), (9, true), (1, false), (8, false), (6, false)],
   [(2, true), (6, true), (2, false), (9, false), (8, false), (7, false), (6, false)],
   [(2, true), (7, true), (2, false), (8, false)],
   [(2, true), (8, true), (2, false), (8, false), (7, false)],
   [(2, true), (9, true), (2, false), (7, false), (6, false)],
   [(3, true), (6, true), (3, false), (9, false), (7, false), (6, false)],
   [(3, true), (7, true), (3, false), (9, false), (8, false), (7, false), (6, false)],
   [(3, true), (8, true), (3, false), (8, false), (7, false), (6, false)],
   [(3, true), (9, true), (3, false), (9, false), (8, false), (7, false)],
   [(4, true), (6, true), (4, false), (8, false)],
   [(4, true), (7, true), (4, false), (9, false), (7, false), (6, false)],
   [(4, true), (8, true), (4, false), (8, false), (6, false)],
   [(4, true), (9, true), (4, false), (8, false), (7, false)],
   [(5, true), (6, true), (5, false), (8, false), (6, false)],
   [(5, true), (7, true), (5, false), (9, false), (8, false), (6, false)],
   [(5, true), (8, true), (5, false), (6, false)],
   [(5, true), (9, true), (5, false), (9, false), (7, false), (6, false)]]

@[expose] def thetaRels8 : List M24Word :=
  [[(10, true), (10, true)],
   [(10, true), (9, true), (0, true), (2, true), (3, false), (5, true), (2, false), (10, true),
    (3, true), (5, false), (4, true), (3, false), (0, false)],
   [(10, true), (6, true), (8, true), (2, true), (1, true), (3, true), (5, false), (4, true),
    (2, false), (10, true), (2, true), (4, false), (1, false), (2, false), (9, false), (8, false),
    (6, false)],
   [(10, true), (9, true), (0, true), (1, true), (2, true), (5, false), (2, true), (10, true),
    (3, false), (4, true), (3, false), (1, false), (0, false)]]

@[expose] def ruRel : List M24Word :=
  [[(10, true), (0, true), (4, false), (3, true), (2, false), (0, true), (5, false), (10, true),
    (5, true), (0, false), (2, true), (3, false), (4, true), (0, false), (10, true), (2, true),
    (0, false), (4, true), (0, false), (9, false), (6, false)]]

@[expose] def relsN8 : List M24Word := carmRels ++ tRels ++ actRels

@[expose] def m24Rels : List M24Word := relsN8 ++ thetaRels8 ++ ruRel

theorem length_relsN8 : relsN8.length = 55 := rfl

theorem length_thetaRels8 : thetaRels8.length = 4 := rfl

theorem length_ruRel : ruRel.length = 1 := rfl

theorem length_m24Rels : m24Rels.length = 60 := rfl

theorem thetaRels8_eq : thetaRels8 = [(letG, true), (letG, true)] ::
    List.ofFn fun i : Fin 3 => (letG, true) :: dWord i ++ (letG, true) :: invW (thetaWord i) := by
  decide

theorem ruRel_eq : ruRel =
    [(letG, true) :: nWord ++ (letG, true) :: invW nWord ++ (letG, true) :: invW wWord] := by
  decide

@[expose] def relsN8Ten : List (List (Fin 10 × Bool)) :=
  [[(0, true), (0, true), (0, true)],
   [(0, true), (1, true), (0, true), (1, true)],
   [(0, true), (2, true), (0, true), (2, true)],
   [(0, true), (3, true), (0, true), (3, true)],
   [(0, true), (4, true), (0, true), (4, true)],
   [(0, true), (5, true), (0, true), (5, true)],
   [(1, true), (1, true), (1, true)],
   [(1, true), (2, true), (1, true), (2, true)],
   [(1, true), (3, true), (1, true), (3, true)],
   [(1, true), (4, true), (1, true), (4, true)],
   [(1, true), (5, true), (1, true), (5, true)],
   [(2, true), (2, true), (2, true)],
   [(2, true), (3, true), (2, true), (3, true)],
   [(2, true), (4, true), (2, true), (4, true)],
   [(2, true), (5, true), (2, true), (5, true)],
   [(3, true), (3, true), (3, true)],
   [(3, true), (4, true), (3, true), (4, true)],
   [(3, true), (5, true), (3, true), (5, true)],
   [(4, true), (4, true), (4, true)],
   [(4, true), (5, true), (4, true), (5, true)],
   [(5, true), (5, true), (5, true)],
   [(6, true), (6, true)],
   [(6, true), (7, true), (6, true), (7, true)],
   [(6, true), (8, true), (6, true), (8, true)],
   [(6, true), (9, true), (6, true), (9, true)],
   [(7, true), (7, true)],
   [(7, true), (8, true), (7, true), (8, true)],
   [(7, true), (9, true), (7, true), (9, true)],
   [(8, true), (8, true)],
   [(8, true), (9, true), (8, true), (9, true)],
   [(9, true), (9, true)],
   [(0, true), (6, true), (0, false), (9, false), (7, false)],
   [(0, true), (7, true), (0, false), (8, false), (7, false)],
   [(0, true), (8, true), (0, false), (7, false)],
   [(0, true), (9, true), (0, false), (9, false), (8, false), (6, false)],
   [(1, true), (6, true), (1, false), (9, false), (8, false), (7, false)],
   [(1, true), (7, true), (1, false), (9, false), (6, false)],
   [(1, true), (8, true), (1, false), (7, false), (6, false)],
   [(1, true), (9, true), (1, false), (8, false), (6, false)],
   [(2, true), (6, true), (2, false), (9, false), (8, false), (7, false), (6, false)],
   [(2, true), (7, true), (2, false), (8, false)],
   [(2, true), (8, true), (2, false), (8, false), (7, false)],
   [(2, true), (9, true), (2, false), (7, false), (6, false)],
   [(3, true), (6, true), (3, false), (9, false), (7, false), (6, false)],
   [(3, true), (7, true), (3, false), (9, false), (8, false), (7, false), (6, false)],
   [(3, true), (8, true), (3, false), (8, false), (7, false), (6, false)],
   [(3, true), (9, true), (3, false), (9, false), (8, false), (7, false)],
   [(4, true), (6, true), (4, false), (8, false)],
   [(4, true), (7, true), (4, false), (9, false), (7, false), (6, false)],
   [(4, true), (8, true), (4, false), (8, false), (6, false)],
   [(4, true), (9, true), (4, false), (8, false), (7, false)],
   [(5, true), (6, true), (5, false), (8, false), (6, false)],
   [(5, true), (7, true), (5, false), (9, false), (8, false), (6, false)],
   [(5, true), (8, true), (5, false), (6, false)],
   [(5, true), (9, true), (5, false), (9, false), (7, false), (6, false)]]

theorem relsN8_eq_map : relsN8 = relsN8Ten.map liftW10 := by
  decide

end CFSG.CGT.M24R
