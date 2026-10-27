module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTab
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelTab

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

namespace Tab

variable {n : ℕ} [NeZero n] (t : Tab n)

@[expose] def isAutB (a : Tbl) : Bool :=
  a.get t.one == t.one &&
  (List.finRange 64).all (fun i => (List.finRange 64).all fun j =>
    a.get (t.mulT i j) == t.mulT (a.get i) (a.get j)) &&
  (List.finRange 64).all (fun i =>
    (List.finRange 64).all fun j => imp (a.get i == a.get j) (i == j))

@[expose] def ofImages (h : Fin 4 → Fin 64) : Tbl :=
  Vector.ofFn fun i => evalW t.mulT t.one h (t.words.get i)

@[expose] def pairOK (x y gx gy : Fin 64) : Bool :=
  t.cls3 (t.mulT x y) == t.cls3 (t.mulT gx gy) && t.cls3 (t.mulT y x) == t.cls3 (t.mulT gy gx)

@[expose] def ok0 (h0 : Fin 64) : Bool := t.cls3 h0 == t.cls3 (t.gens.get 0)

@[expose] def ok1 (h0 h1 : Fin 64) : Bool :=
  t.cls3 h1 == t.cls3 (t.gens.get 1) && t.pairOK h0 h1 (t.gens.get 0) (t.gens.get 1)

@[expose] def ok2 (h0 h1 h2 : Fin 64) : Bool :=
  t.cls3 h2 == t.cls3 (t.gens.get 2) && t.pairOK h0 h2 (t.gens.get 0) (t.gens.get 2) &&
    t.pairOK h1 h2 (t.gens.get 1) (t.gens.get 2)

@[expose] def ok3 (h0 h1 h2 h3 : Fin 64) : Bool :=
  t.cls3 h3 == t.cls3 (t.gens.get 3) && t.pairOK h0 h3 (t.gens.get 0) (t.gens.get 3) &&
    t.pairOK h1 h3 (t.gens.get 1) (t.gens.get 3) && t.pairOK h2 h3 (t.gens.get 2) (t.gens.get 3)

@[expose] def autsOf : List Tbl :=
  ((List.finRange 64).filter t.ok0).flatMap fun h0 =>
    ((List.finRange 64).filter (t.ok1 h0)).flatMap fun h1 =>
      ((List.finRange 64).filter (t.ok2 h0 h1)).flatMap fun h2 =>
        (((List.finRange 64).filter (t.ok3 h0 h1 h2)).filter
          fun h3 => t.isAutB (t.ofImages ![h0, h1, h2, h3])).map
            fun h3 => t.ofImages ![h0, h1, h2, h3]

@[expose] def edge (a : Tbl) (i j : Fin 64) : Bool :=
  t.isInv i && t.isInv j && (t.cls.get i == t.cls.get j || a.get i == j)

@[expose] def step (a : Tbl) (S : Vector Bool 64) : Vector Bool 64 :=
  Vector.ofFn fun j => S.get j || (List.finRange 64).any fun i => S.get i && t.edge a i j

@[expose] def reach (a : Tbl) (s0 : Fin 64) : Vector Bool 64 :=
  (t.step a)^[12] (Vector.ofFn fun j => j == s0)

@[expose] def wB (a : Tbl) : Bool :=
  !t.useW ||
  (let z := t.el.get (a.get t.x0i)
   let O := t.o3.filter fun σ => decide (σ * z.1 = z.1 * σ)
   O.isEmpty || O.any fun σ' => (List.finRange 64).all fun q =>
     imp (t.isQ.get q && decide (t.el.get q * z = z * t.el.get q))
       (decide ((t.el.get (a.get q)).1 * σ' = σ' * (t.el.get (a.get q)).1)))

@[expose] def certB (a : Tbl) (X0 V0 : Vector Bool 64) (s : Fin 64) (ψ : Tbl) : Bool :=
  ψ.get t.x0i == t.x0i &&
  (List.finRange 64).all (fun i =>
    ψ.get (t.mulT (t.mulT s (a.get i)) (t.inv.get s)) == t.astar.get (ψ.get i)) &&
  (List.finRange 64).all (fun i => imp (t.isInv i)
    (imp (X0.get i) (t.nm.get (ψ.get i) == 4) && imp (V0.get i) (t.nm.get (ψ.get i) == 8)))

@[expose] def finalB (L : List Tbl) (a : Tbl) : Bool :=
  imp (a.get t.x0i != t.x0i) <|
  (List.finRange 64).all fun u =>
    imp (a.get u == u && (List.finRange 64).all fun i =>
        a.get (a.get i) == t.mulT (t.mulT u i) (t.inv.get u)) <|
    let X0 := t.reach a t.x0i
    let V0 := t.reach a (t.mulT t.x0i (a.get t.x0i))
    imp ((List.finRange 64).all fun i => !(X0.get i && V0.get i)) <|
    imp ((List.finRange 64).all fun i => imp (t.isQ.get i && i != t.one) (!V0.get i)) <|
    imp (t.wB a) <|
      (List.finRange 64).all (fun i => imp (t.isInv i) (X0.get i || V0.get i)) &&
      (List.finRange 64).any fun s =>
        t.mulT (t.mulT s (a.get s)) u == t.one && L.any fun ψ => t.certB a X0 V0 s ψ

@[expose] def claimB : Bool :=
  let L := t.autsOf
  (List.finRange 64).all fun h0 => imp (t.ok0 h0) <|
  (List.finRange 64).all fun h1 => imp (t.ok1 h0 h1) <|
  (List.finRange 64).all fun h2 => imp (t.ok2 h0 h1 h2) <|
  (List.finRange 64).all fun h3 => imp (t.ok3 h0 h1 h2 h3) <|
    let a := t.ofImages ![h0, h1, h2, h3]
    imp (t.isAutB a) (t.finalB L a)

end Tab

end CFSG.GH74.GLS.C3.Layer2.Model
