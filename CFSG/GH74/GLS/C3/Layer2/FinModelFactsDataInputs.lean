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

open Equiv Perm CFSG.GH74.GLS.C3.Layer2
namespace Facts

@[expose] def flatPermAux {m : ℕ} (p : Perm (Fin m)) (t s : Array (Fin m))
    (ht : t = Array.ofFn p) (hs : s = Array.ofFn p.symm) : Perm (Fin m) where
  toFun i := t[i.1]'(by subst ht; simp)
  invFun i := s[i.1]'(by subst hs; simp)
  left_inv i := by subst ht hs; simp
  right_inv i := by subst ht hs; simp

@[expose] def flatPerm {m : ℕ} (p : Perm (Fin m)) : Perm (Fin m) :=
  flatPermAux p (Array.ofFn p) (Array.ofFn p.symm) rfl rfl

@[expose] def evalWord {m r : ℕ} (y : Fin r → Perm (Fin m)) (w : List (Fin r)) : Perm (Fin m) :=
  flatPerm (w.map y).prod

@[expose] def bfsStep {m r : ℕ} (g : Fin r → Perm (Fin m))
    (l : List (Perm (Fin m) × List (Fin r))) : List (Perm (Fin m) × List (Fin r)) :=
  l.foldl (fun acc pw => (List.finRange r).foldl (fun acc k =>
    let q := flatPerm (pw.1 * g k)
    if acc.any (fun x => decide (x.1 = q)) then acc else acc ++ [(q, pw.2 ++ [k])]) acc) l

@[expose] def bfsTab {m r : ℕ} (g : Fin r → Perm (Fin m)) (k : ℕ) :
    List (Perm (Fin m) × List (Fin r)) :=
  (bfsStep g)^[k] [(1, [])]

@[expose] def wordOf {m r : ℕ} (tab : List (Perm (Fin m) × List (Fin r))) (p : Perm (Fin m)) :
    List (Fin r) :=
  ((tab.find? fun x => decide (x.1 = p)).map Prod.snd).getD []

@[expose] def Rl (n : ℕ) [NeZero n] : List (Perm (Fin (n + 4))) :=
  (Tl n).map fun t => flatPerm (emb n t)

@[expose] def a0f (n : ℕ) [NeZero n] : Perm (Fin (n + 4)) := flatPerm (a0perm n)

@[expose] def y0p (n : ℕ) [NeZero n] : Perm (Fin (n + 4)) := flatPerm (emb n (x0 n))

@[expose] def Sl (n : ℕ) [NeZero n] : List (Perm (Fin (n + 4))) :=
  Rl n ++ (Rl n).map fun p => flatPerm (p * a0f n)

@[expose] def Cl (n : ℕ) [NeZero n] : List (Perm (Fin (n + 4))) :=
  (Sl n).filter fun p => decide (a0f n * p = p * a0f n)

@[expose] def gensPair (n : ℕ) [NeZero n] : Perm (Fin (n + 4)) × Perm (Fin (n + 4)) :=
  let cl := Cl n
  let cands : List (Perm (Fin (n + 4)) × Perm (Fin (n + 4))) :=
    cl.flatMap fun p => cl.map fun q => (p, q)
  (cands.find? fun pq => (bfsTab ![a0f n, pq.1, pq.2] 6).length == cl.length).getD (1, 1)

@[expose] def wordsB {m r : ℕ} (g : Fin r → Perm (Fin m)) (cl : List (Perm (Fin m)))
    (wd : Perm (Fin m) → List (Fin r)) : Bool :=
  cl.all fun w => decide (evalWord g (wd w) = w)

@[expose] def exOf {m : ℕ} (rl : List (Perm (Fin m))) : Perm (Fin m) → ℕ :=
  fun p => if p ∈ rl then numMoved p else 4

@[expose] def stepsOf {m : ℕ} (wd : Perm (Fin m) → List (Fin 3)) (cl : List (Perm (Fin m)))
    (g : Fin 3 → Perm (Fin m)) : List (List (Fin 3) × Fin 3 × List (Fin 3)) :=
  cl.flatMap fun p => (List.finRange 3).map fun k => (wd p, k, wd (flatPerm (p * g k)))

@[expose] def invsOf {m : ℕ} (wd : Perm (Fin m) → List (Fin 3)) (ex : Perm (Fin m) → ℕ)
    (cl : List (Perm (Fin m))) : List (List (Fin 3) × ℕ) :=
  (cl.filter fun p => decide (p * p = 1 ∧ p ≠ 1)).map fun p => (wd p, ex p)

@[expose] def homB {m : ℕ} (steps : List (List (Fin 3) × Fin 3 × List (Fin 3)))
    (y : Fin 3 → Perm (Fin m)) : Bool :=
  steps.all fun x => decide (evalWord y x.2.2 = evalWord y x.1 * y x.2.1)

@[expose] def injB {m : ℕ} (cl : List (Perm (Fin m))) (wd : Perm (Fin m) → List (Fin 3))
    (y : Fin 3 → Perm (Fin m)) : Bool :=
  decide ((cl.map fun p => evalWord y (wd p)).Nodup)

@[expose] def valB {m : ℕ} (invs : List (List (Fin 3) × ℕ)) (y : Fin 3 → Perm (Fin m)) : Bool :=
  invs.all fun x => decide (numMoved (evalWord y x.1) = x.2)

@[expose] def etaB {m : ℕ} (rl cl : List (Perm (Fin m))) (g : Fin 3 → Perm (Fin m))
    (y0 : Perm (Fin m)) (wd : Perm (Fin m) → List (Fin 3)) (ex : Perm (Fin m) → ℕ) : Bool :=
  let steps := stepsOf wd cl g
  let invs := invsOf wd ex cl
  rl.all fun y1 => rl.all fun y2 =>
    !homB steps ![y0, y1, y2] || !injB cl wd ![y0, y1, y2] || !valB invs ![y0, y1, y2]

@[expose] def etaFullTab {m : ℕ} (rl cl : List (Perm (Fin m))) (g : Fin 3 → Perm (Fin m))
    (y0 : Perm (Fin m)) (tab : List (Perm (Fin m) × List (Fin 3))) : Bool :=
  wordsB g cl (wordOf tab) && etaB rl cl g y0 (wordOf tab) (exOf rl)

@[expose] def etaFullOf {m : ℕ} (rl cl : List (Perm (Fin m))) (g : Fin 3 → Perm (Fin m))
    (y0 : Perm (Fin m)) : Bool :=
  etaFullTab rl cl g y0 (bfsTab g 6)

@[expose] def etaFull (n : ℕ) [NeZero n] : Bool :=
  let pq := gensPair n
  let cl := Cl n
  decide (pq.1 ∈ cl) && decide (pq.2 ∈ cl) && decide (a0f n ∈ cl) &&
    etaFullOf (Rl n) cl ![a0f n, pq.1, pq.2] (y0p n)

@[expose] def sqB (n : ℕ) [NeZero n] : Bool := decide (a0f n * a0f n = 1)

@[expose] def notinB (n : ℕ) [NeZero n] : Bool := !decide (a0f n ∈ Rl n)

@[expose] def normB (n : ℕ) [NeZero n] : Bool :=
  let rl := Rl n
  rl.all fun p => decide (flatPerm (a0f n * p * (a0f n)⁻¹) ∈ rl)

@[expose] def oddB (n : ℕ) [NeZero n] : Bool :=
  (Rl n).all fun p =>
    let q := flatPerm (p * a0f n)
    decide (q * q = 1 → q ≠ 1 → numMoved q = 8)

@[expose] def conjB (n : ℕ) [NeZero n] : Bool :=
  let rl := Rl n
  rl.all fun p =>
    let q := flatPerm (p * a0f n)
    !decide (q * q = 1) || rl.any fun r => decide (flatPerm (r * a0f n * r⁻¹) = q)

@[expose] def nodupB (n : ℕ) [NeZero n] : Bool := decide ((Sl n).Nodup)

@[expose] def centB (n : ℕ) [NeZero n] : Bool :=
  let sl := Sl n
  let y0 := y0p n
  let a := a0f n
  sl.all fun y =>
    decide (y * y = 1 → y ≠ 1 → (sl.filter fun p => decide (y * p = p * y)).length = 64 →
      y = y0 ∨ y = flatPerm (a * y0 * a⁻¹))

@[expose] def allB (n : ℕ) [NeZero n] : Bool :=
  sqB n && notinB n && normB n && oddB n && conjB n && nodupB n && centB n && etaFull n

end Facts

end CFSG.GH74.GLS.C3.Layer2.Model
