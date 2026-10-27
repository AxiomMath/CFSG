module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

structure PSimple where
  par : List ℕ
  gen : List Bool
  suc1 : List ℕ
  suc2 : List ℕ
  cls : List (Option (ℕ × ℕ))
  reps : List ℕ
  nc : List (List ℕ × List ℕ)
  o1 : ℕ
  o2 : ℕ
  k3 : ℕ
  kz : ℕ

namespace PSimple

variable {G : Type*} [Group G]

@[expose] def elemsAux (c : PSimple) (g1 g2 : G) : ℕ → List G
  | 0 => []
  | n + 1 =>
    let acc := elemsAux c g1 g2 n
    acc ++ [if n = 0 then 1 else
      acc.getD (c.par.getD n 0) 1 * (if c.gen.getD n false then g2 else g1)]

@[expose] def elems (c : PSimple) (g1 g2 : G) : List G := c.elemsAux g1 g2 c.par.length

@[expose] def check [DecidableEq G] (c : PSimple) (g1 g2 z : G) : Bool :=
  let n := c.par.length
  let s := c.elems g1 g2
  let S : ℕ → G := fun k => s.getD k 1
  decide (0 < n) && decide (c.gen.length = n) && decide (c.suc1.length = n) &&
  decide (c.suc2.length = n) && decide (c.cls.length = n) && decide (0 < c.o1) &&
  decide (0 < c.o2) && decide (g1 ^ c.o1 = 1) && decide (g2 ^ c.o2 = 1) &&
  (List.range n).all (fun k =>
    decide (k = 0 ∨ c.par.getD k 0 < k) &&
    decide (c.suc1.getD k 0 < n) && decide (c.suc2.getD k 0 < n) &&
    decide (S k * g1 = S (c.suc1.getD k 0)) && decide (S k * g2 = S (c.suc2.getD k 0)) &&
    (match c.cls.getD k none with
      | none => decide (S k = 1)
      | some (u, i) => decide (u < n) && decide (i < c.reps.length) &&
          decide (S k * S u = S u * S (c.reps.getD i 0)))) &&
  c.reps.all (fun r => decide (r < n)) &&
  (List.range c.reps.length).all (fun i =>
    (c.nc.getD i ([], [])).1.all (fun l => decide (l < n) &&
      decide ((c.cls.getD l none).map Prod.snd = some i)) &&
    (c.nc.getD i ([], [])).2.all (fun l => decide (l < n) &&
      decide ((c.cls.getD l none).map Prod.snd = some i)) &&
    decide ((((c.nc.getD i ([], [])).1).map S).prod = g1) &&
    decide ((((c.nc.getD i ([], [])).2).map S).prod = g2)) &&
  decide (g1 * g2 ≠ g2 * g1) && decide (S c.k3 ^ 3 = 1) && decide (S c.k3 ≠ 1) &&
  decide (S c.kz = z)

end PSimple

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
