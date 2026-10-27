module

public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ComponentClassification.GSThmB.Cat81A8

theorem getD_ofFn (σ : Fin 8 → Fin 8) (i : Fin 8) : (List.ofFn σ).getD i 0 = σ i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

@[expose] def ofTab (σ : Equiv.Perm (Fin 8)) : Equiv.Perm (Fin 8) :=
  let t := List.ofFn σ
  let u := List.ofFn σ.symm
  { toFun := fun i => t.getD i 0
    invFun := fun i => u.getD i 0
    left_inv := fun i => by simp only [t, u, getD_ofFn, Equiv.symm_apply_apply]
    right_inv := fun i => by simp only [t, u, getD_ofFn, Equiv.apply_symm_apply] }

theorem ofTab_eq (σ : Equiv.Perm (Fin 8)) : ofTab σ = σ :=
  Equiv.ext fun i => getD_ofFn σ i

@[expose] def bfsStep (gens L : List (Equiv.Perm (Fin 8))) : List (Equiv.Perm (Fin 8)) :=
  (L ++ L.flatMap fun a => gens.map fun g => ofTab (a * g)).dedup

@[expose] def bfs (gens : List (Equiv.Perm (Fin 8))) : ℕ → List (Equiv.Perm (Fin 8))
  | 0 => [1]
  | k + 1 => bfsStep gens (bfs gens k)

@[expose] def tr : Equiv.Perm (Fin 8) := List.formPerm [0, 1, 2, 3]

@[expose] def ts : Equiv.Perm (Fin 8) := List.formPerm [0, 2]

@[expose] def tw : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 4] * List.formPerm [1, 5] * List.formPerm [2, 6] * List.formPerm [3, 7]

@[expose] def gensT : List (Equiv.Perm (Fin 8)) := [tr, ts, tw]

@[expose] def TList : List (Equiv.Perm (Fin 8)) := bfs gensT 8

@[expose] def closedUnder (gens L : List (Equiv.Perm (Fin 8))) : Bool :=
  L.all fun a => gens.all fun g => L.contains (a * g)

@[expose] def invComm (x : Equiv.Perm (Fin 8)) : List (Equiv.Perm (Fin 8)) :=
  TList.filter fun y => decide (y * y = 1) && decide (x * y = y * x)

@[expose] def bigInv : List (Equiv.Perm (Fin 8)) :=
  TList.filter fun x => decide (x * x = 1) && !decide (x = 1) && decide (32 ≤ (invComm x).length)

@[expose] def lx : Equiv.Perm (Fin 8) := List.formPerm [5, 7]

@[expose] def ly : Equiv.Perm (Fin 8) := List.formPerm [4, 5] * List.formPerm [6, 7]

@[expose] def lq : Equiv.Perm (Fin 8) := tr * List.formPerm [4, 5, 6, 7]

end CFSG.ComponentClassification.GSThmB.Cat81A8
