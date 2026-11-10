module

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2
abbrev Tbl : Type := Vector (Fin 64) 64

@[expose, macro_inline] def imp (p q : Bool) : Bool :=
  match p with
  | true => q
  | false => true

@[expose] def evalW (mul : Fin 64 → Fin 64 → Fin 64) (one : Fin 64) (h : Fin 4 → Fin 64) :
    List (Fin 4) → Fin 64
  | [] => one
  | k :: w => mul (h k) (evalW mul one h w)

@[expose] def keyA (n : ℕ) (g : Amb n) : List ℕ :=
  (List.finRange n).map (fun i => ((g.1 i : Fin n) : ℕ)) ++
    (List.finRange 4).map (fun j => ((g.2 j : Fin 4) : ℕ))

@[expose] def dcls (d : Perm (Fin 4)) : ℕ :=
  if d = 1 then 0 else if d = x4 then 1 else if numMoved d = 4 then 2 else 3

@[expose] def clsOf (n : ℕ) (g : Amb n) : ℕ := numMoved g.1 * 4 + dcls g.2

@[expose] def cyc3 {n : ℕ} (a b c : Fin n) : Perm (Fin n) := swap a b * swap b c

@[expose] def triples (n : ℕ) : List (Fin n × Fin n × Fin n) :=
  (List.finRange n).flatMap fun a => (List.finRange n).flatMap fun b =>
    (List.finRange n).filterMap fun c => if a < b ∧ b < c then some (a, b, c) else none

@[expose] def o3List (n : ℕ) : List (Perm (Fin n)) :=
  let ts := triples n
  (ts.flatMap fun (a, b, c) => [cyc3 a b c, cyc3 a c b]) ++
    ts.flatMap fun (a, b, c) => ts.flatMap fun (d, e, f) =>
      if a < d ∧ a ≠ e ∧ a ≠ f ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧ c ≠ f then
        [cyc3 a b c * cyc3 d e f, cyc3 a c b * cyc3 d e f, cyc3 a b c * cyc3 d f e,
          cyc3 a c b * cyc3 d f e]
      else []

@[expose] def wordsOf (mul : Vector (Vector (Fin 64) 64) 64) (one : Fin 64)
    (gens : Vector (Fin 64) 4) : Vector (List (Fin 4)) 64 :=
  let step (w : Vector (Option (List (Fin 4))) 64) : Vector (Option (List (Fin 4))) 64 :=
    (List.finRange 64).foldl (fun w i =>
      match w.get i with
      | none => w
      | some l => (List.finRange 4).foldl (fun w k =>
          let j := (mul.get i).get (gens.get k)
          match w.get j with
          | none => w.set j.1 (some (l ++ [k])) j.2
          | some _ => w) w) w
  let w0 : Vector (Option (List (Fin 4))) 64 :=
    (Vector.replicate 64 none).set one.1 (some []) one.2
  let wf := step^[8] w0
  Vector.ofFn fun i => (wf.get i).getD []

structure Tab (n : ℕ) [NeZero n] where
  el : Vector (Amb n) 64
  mul : Vector (Vector (Fin 64) 64) 64
  inv : Tbl
  one : Fin 64
  x0i : Fin 64
  gens : Vector (Fin 64) 4
  words : Vector (List (Fin 4)) 64
  cls : Vector ℕ 64
  rep : Tbl
  isQ : Vector Bool 64
  nm : Vector ℕ 64
  astar : Tbl
  useW : Bool
  o3 : List (Perm (Fin n))

namespace Tab

variable {n : ℕ} [NeZero n] (t : Tab n)

@[expose] def mulT (i j : Fin 64) : Fin 64 := (t.mul.get i).get j

@[expose] def isInv (i : Fin 64) : Bool := i != t.one && t.mulT i i == t.one

end Tab

@[expose] def mkTab (n : ℕ) [NeZero n] : Tab n :=
  let el : Vector (Amb n) 64 := Vector.ofFn fun i => (Tl n).getD i.1 1
  let keys : List (List ℕ) := (List.finRange 64).map fun i => keyA n (el.get i)
  let idx : Amb n → Fin 64 := fun g => ⟨keys.idxOf (keyA n g) % 64, Nat.mod_lt _ (by decide)⟩
  let mul : Vector (Vector (Fin 64) 64) 64 :=
    Vector.ofFn fun i => Vector.ofFn fun j => idx (el.get i * el.get j)
  let one : Fin 64 := idx 1
  let inv : Tbl := Vector.ofFn fun i => idx (el.get i)⁻¹
  let gens : Vector (Fin 64) 4 := Vector.ofFn (![6, 0, 2, 8] : Fin 4 → Fin 64)
  let cls : Vector ℕ 64 := Vector.ofFn fun i => clsOf n (el.get i)
  let isInvB : Fin 64 → Bool := fun i => i != one && (mul.get i).get i == one
  let em : Vector (Perm (Fin (n + 4))) 64 := Vector.ofFn fun i => emb n (el.get i)
  { el := el
    mul := mul
    inv := inv
    one := one
    x0i := idx (x0 n)
    gens := gens
    words := wordsOf mul one gens
    cls := cls
    rep := Vector.ofFn fun i =>
      ((List.finRange 64).find? fun j => isInvB j && cls.get j == cls.get i).getD i
    isQ := Vector.ofFn fun i => decide ((el.get i).1 = 1)
    nm := Vector.ofFn fun i => numMoved (em.get i)
    astar := Vector.ofFn fun i =>
      ((List.finRange 64).find? fun j =>
        decide (em.get j = a0perm n * em.get i * (a0perm n)⁻¹)).getD i
    useW := decide (n = 7)
    o3 := o3List n }

@[expose] def Tab.checks {n : ℕ} [NeZero n] (t : Tab n) : List Bool :=
  let L := Tl n
  [(List.finRange 64).all (fun i => decide (t.el.get i ∈ L)),
  L.all (fun g => (List.finRange 64).any fun i => decide (t.el.get i = g)),
  (List.finRange 64).all (fun i => (List.finRange 64).all fun j =>
    imp (decide (t.el.get i = t.el.get j)) (i == j)),
  (List.finRange 64).all (fun i => (List.finRange 64).all fun j =>
    decide (t.el.get (t.mulT i j) = t.el.get i * t.el.get j)),
  decide (t.el.get t.one = 1),
  (List.finRange 64).all (fun i => decide (t.el.get (t.inv.get i) = (t.el.get i)⁻¹)),
  decide (t.el.get t.x0i = x0 n),
  (List.finRange 64).all (fun i => evalW t.mulT t.one t.gens.get (t.words.get i) == i),
  (List.finRange 64).all (fun i => (List.finRange 64).all fun j =>
    imp (t.isInv i && t.isInv j && t.cls.get i == t.cls.get j) (t.rep.get i == t.rep.get j)),
  (List.finRange 64).all (fun j => imp (t.isInv j)
    (decide (∃ σ : Perm (Fin n), σ * (t.el.get (t.rep.get j)).1 * σ⁻¹ = (t.el.get j).1 ∧
      ∃ d ∈ Dl, d * (t.el.get (t.rep.get j)).2 * d⁻¹ = (t.el.get j).2 ∧ sign σ = sign d))),
  (List.finRange 64).all (fun i => (t.isQ.get i == true) == decide ((t.el.get i).1 = 1)),
  (List.finRange 64).all (fun i => t.nm.get i == numMoved (emb n (t.el.get i))),
  (List.finRange 64).all (fun i => decide (a0perm n * emb n (t.el.get i) * (a0perm n)⁻¹ =
    emb n (t.el.get (t.astar.get i)))),
  decide (∀ σ : Perm (Fin n), σ ≠ 1 → σ * σ * σ = 1 → σ ∈ t.o3),
  t.o3.all (fun σ => decide (σ ≠ 1 ∧ σ * σ * σ = 1)),
  (t.useW == decide (n = 7))]

@[expose] def Tab.validB {n : ℕ} [NeZero n] (t : Tab n) : Bool := t.checks.all id

end CFSG.GH74.GLS.C3.Layer2.Model
