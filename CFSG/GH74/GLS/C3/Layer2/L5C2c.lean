module

public import CFSG.GH74.GLS.C3.Layer2.L5C2b
public import CFSG.GH74.GLS.C3.Layer2.L5C0

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

variable {n : Nat} [Group (Idx n)]

@[expose] def isInv (u : Idx n) : Bool := decide (u * u = 1) && decide (u ≠ 1)

@[expose] def evW (gs : List (Idx n)) (w : List Nat) : Idx n :=
  w.foldl (fun a i => a * gs.getD i 1) 1

@[expose] def cszI (u : Idx n) : Nat :=
  ((elemsI n).filter fun s => decide (s * u = u * s)).length

@[expose] def addNew (vis : Array Bool) (new : List (Idx n)) (ys : List (Idx n)) :
    Array Bool × List (Idx n) :=
  ys.foldl (fun (st : Array Bool × List (Idx n)) y =>
    if st.1.getD y.v false then st else (st.1.set! y.v true, y :: st.2)) (vis, new)

@[expose] def bfsGo (steps : Idx n → List (Idx n)) :
    Nat → Array Bool → List (Idx n) → List (Idx n) → List (Idx n)
  | 0, _, _, acc => acc
  | fuel + 1, vis, frontier, acc =>
    match frontier with
    | [] => acc
    | _ =>
      let st := frontier.foldl
        (fun (st : Array Bool × List (Idx n)) x => addNew st.1 st.2 (steps x)) (vis, [])
      bfsGo steps fuel st.1 st.2 (acc ++ st.2)

@[expose] def bfs (steps : Idx n → List (Idx n)) (r : Idx n) : List (Idx n) :=
  bfsGo steps n ((Array.replicate n false).set! r.v true) [r] [r]

@[expose] def allT5L : List ↥T5 :=
  allT5.pmap (fun t ht => (⟨t, mem_allT5.1 ht⟩ : ↥T5)) (fun _ h => h)

@[expose] def f5Pairs (emb : ↥T5 →* Idx n) : List (Idx n × Idx n) :=
  allT5L.flatMap fun (t : ↥T5) => F5list.filterMap fun g =>
    if h : T5b (g * (t : Amb 5) * g⁻¹) = true then
      some (emb t, emb ⟨g * (t : Amb 5) * g⁻¹, mem_T5_of_b h⟩)
    else none

@[expose] def nbarPairs
    (emb : ↥T5 →* Idx n) : List (Idx n × Idx n) :=
  n24L.flatMap fun A => (List.finRange 16).map fun i => (emb (elT i), emb (elT (A i)))

@[expose] def dedupPairs (ps : List (Idx n × Idx n)) : List (Idx n × Idx n) :=
  (ps.foldl (fun (st : Array Bool × List (Idx n × Idx n)) p =>
    if st.1.getD (p.1.v * n + p.2.v) false then st
    else (st.1.set! (p.1.v * n + p.2.v) true, p :: st.2)) (Array.replicate (n * n) false, [])).2

@[expose] def fuseOf
    (emb : ↥T5 →* Idx n) : List (Idx n × Idx n) :=
  dedupPairs ((f5Pairs emb ++ nbarPairs emb).filter fun p => isInv p.1 && isInv p.2)

@[expose] def stepsOf (fuse : List (Idx n × Idx n)) (x : Idx n) : List (Idx n) :=
  (elemsI n).map (fun s => s * x * s⁻¹) ++
    fuse.filterMap fun p => if p.1 = x then some p.2 else if p.2 = x then some p.1 else none

@[expose] def markAll (cov : Array Bool) (l : List (Idx n)) : Array Bool :=
  l.foldl (fun c m => c.set! m.v true) cov

@[expose] def repsGo (steps : Idx n → List (Idx n)) :
    List (Idx n) → Array Bool → List (Idx n) → List (Idx n)
  | [], _, acc => acc.reverse
  | u :: us, cov, acc =>
    if cov.getD u.v false then repsGo steps us cov acc
    else repsGo steps us (markAll cov (bfs steps u)) (u :: acc)

@[expose] def ciArrOf (members : List (List (Idx n))) : Array Nat :=
  members.zipIdx.foldl (fun (arr : Array Nat) (p : List (Idx n) × Nat) =>
    p.1.foldl (fun a m => a.set! m.v p.2) arr) (Array.replicate n 0)

@[expose] def wordsGo (gs : List (Idx n)) :
    Nat → Array Bool → List (Idx n × List Nat) → List (Idx n × List Nat) →
      List (Idx n × List Nat)
  | 0, _, _, acc => acc
  | fuel + 1, vis, frontier, acc =>
    match frontier with
    | [] => acc
    | _ =>
      let st := frontier.foldl
        (fun (st : Array Bool × List (Idx n × List Nat)) (ew : Idx n × List Nat) =>
          (List.range gs.length).foldl
            (fun (st : Array Bool × List (Idx n × List Nat)) (i : Nat) =>
              let e' := ew.1 * gs.getD i 1
              if st.1.getD e'.v false then st
              else (st.1.set! e'.v true, (e', ew.2 ++ [i]) :: st.2)) st) (vis, [])
      wordsGo gs fuel st.1 st.2.reverse (acc ++ st.2.reverse)

@[expose] def wordsOf (gs : List (Idx n)) : List (Idx n × List Nat) :=
  wordsGo gs n ((Array.replicate n false).set! (1 : Idx n).v true) [(1, [])] [(1, [])]

@[expose] def relsOf (gs : List (Idx n)) (W : List (Idx n × List Nat)) :
    List (List Nat × List Nat) :=
  let wa : Array (Option (List Nat)) :=
    W.foldl (fun a ew => a.set! ew.1.v (some ew.2)) (Array.replicate n none)
  W.flatMap fun ew => (List.range gs.length).filterMap fun i =>
    match wa.getD (ew.1 * gs.getD i 1).v none with
    | some w' => if decide (w' = ew.2 ++ [i]) then none else some (ew.2 ++ [i], w')
    | none => none

@[expose] def greedyGens (S init : List (Idx n)) : List (Idx n) :=
  S.foldl (fun gs s => if (wordsOf gs).any (fun p => decide (p.1 = s)) then gs else gs ++ [s]) init

structure HomCtx (n : Nat) where
  gens : List (Idx n)
  W : List (List (List Nat))
  R : List (List (List Nat × List Nat))

instance {n : Nat} : Inhabited (HomCtx n) := ⟨⟨[], [], []⟩⟩

@[expose] def mkHomCtx (t : Idx n) : HomCtx n :=
  let S := (elemsI n).filter fun s => decide (s * t = t * s)
  let gens := greedyGens S [t]
  { gens := gens
    W := (List.range gens.length).map fun j => (wordsOf (gens.take (j + 1))).map Prod.snd
    R := (List.range gens.length).map fun j =>
      relsOf (gens.take (j + 1)) (wordsOf (gens.take (j + 1))) }

@[expose] def ctxOK (t : Idx n) (c : HomCtx n) : Bool :=
  decide (c.gens.getD 0 1 = t) && c.gens.all (fun g => decide (g * t = t * g)) &&
    (List.range c.gens.length).all fun j =>
      (c.R.getD j []).all fun r =>
        decide (evW (c.gens.take (j + 1)) r.1 = evW (c.gens.take (j + 1)) r.2)

@[expose] def allVecs : Nat → List (List Bool)
  | 0 => [[]]
  | r + 1 => (allVecs r).flatMap fun v => [v ++ [false], v ++ [true]]

@[expose] def wordArrOf (gs : List (Idx n)) : Array (List Nat) :=
  (wordsOf gs).foldl (fun a ew => a.set! ew.1.v ew.2) (Array.replicate n [])

@[expose] def chiV (wordA : Array (List Nat)) (v : List Bool) (m : Idx n) : Bool :=
  (wordA.getD m.v []).foldl (fun acc i => xor acc (v.getD i false)) false

@[expose] def charValid (mgens : List (Idx n)) (wordA : Array (List Nat)) (v : List Bool) : Bool :=
  !(chiV wordA v (1 : Idx n)) && (elemsI n).all fun m => (List.range mgens.length).all fun i =>
    decide (chiV wordA v (m * mgens.getD i 1) = xor (chiV wordA v m) (v.getD i false))

@[expose] def maxSubsOf (mgens : List (Idx n)) (wordA : Array (List Nat)) : List (Array Bool) :=
  ((allVecs mgens.length).filter (charValid mgens wordA)).map fun v =>
    ((elemsI n).map fun m => !(chiV wordA v m)).toArray

structure Eng (n : Nat) where
  reps : List (Idx n)
  members : List (List (Idx n))
  ciA : Array Nat
  cszA : Array Nat
  invs : List (Idx n)
  ctxs : List (HomCtx n)
  mgens : List (Idx n)
  wordA : Array (List Nat)
  maxSubs : List (Array Bool)
  x : Idx n

@[expose] def mkEng
    (emb : ↥T5 →* Idx n) : Eng n :=
  let invs := (elemsI n).filter isInv
  let steps := stepsOf (fuseOf emb)
  let reps := repsGo steps invs (Array.replicate n false) []
  let members := reps.map (bfs steps)
  let mgens := greedyGens (elemsI n) []
  let wordA := wordArrOf mgens
  { reps := reps
    members := members
    ciA := ciArrOf members
    cszA := ((elemsI n).map cszI).toArray
    invs := invs
    ctxs := reps.map mkHomCtx
    mgens := mgens
    wordA := wordA
    maxSubs := maxSubsOf mgens wordA
    x := emb x0T5 }

@[expose] def Eng.K (e : Eng n) : Nat := e.reps.length

@[expose] def engOK (e : Eng n) : Bool :=
  e.reps.all isInv &&
  (List.range e.reps.length).all (fun k => decide (e.ciA.getD (e.reps.getD k 1).v 0 = k)) &&
  e.invs.all (fun u => decide (e.ciA.getD u.v 0 < e.reps.length) &&
    (e.members.getD (e.ciA.getD u.v 0) []).contains u) &&
  (elemsI n).all (fun a => decide (e.cszA.getD a.v 0 = cszI a)) &&
  (elemsI n).all (fun m => decide (evW e.mgens (e.wordA.getD m.v []) = m)) &&
  (List.range e.reps.length).all (fun k => ctxOK (e.reps.getD k 1) (e.ctxs.getD k default)) &&
  isInv e.x

@[expose] def blkOf (ci : Array Nat) (ld : List Nat) (u : Idx n) : Nat := ld.getD (ci.getD u.v 0) 0

@[expose] def cvalOf (e : Eng n) (ld : List Nat) (b : Nat) : Nat :=
  e.invs.foldl (fun m i => if blkOf e.ciA ld i = b then max m (e.cszA.getD i.v 0) else m) 0

@[expose] def tpOf (e : Eng n) (ld : List Nat) (b : Nat) : Idx n :=
  (e.invs.find? fun i =>
    decide (blkOf e.ciA ld i = b) && decide (e.cszA.getD i.v 0 = cvalOf e ld b)).getD 1

@[expose] def xOK (e : Eng n) (ld : List Nat) : Bool :=
  e.invs.all fun i => !decide (blkOf e.ciA ld i = blkOf e.ciA ld e.x) ||
    decide (e.cszA.getD i.v 0 ≤ 32)

@[expose] def thompsonOK (e : Eng n) (ld : List Nat) : Bool :=
  e.maxSubs.all fun H => e.invs.all fun u => H.getD u.v false ||
    e.invs.any fun i => H.getD i.v false && decide (blkOf e.ciA ld i = blkOf e.ciA ld u) &&
      decide (e.cszA.getD i.v 0 = cvalOf e ld (blkOf e.ciA ld u))

@[expose] def candOK (ctx : HomCtx n) (ci : Array Nat) (ld : List Nat) (j : Nat)
    (cs : List (Idx n)) : Bool :=
  (ctx.R.getD (j - 1) []).all (fun r => decide (evW cs r.1 = evW cs r.2)) &&
  (ctx.W.getD (j - 1) []).all fun w =>
    (decide (evW (ctx.gens.take j) w = 1) || decide (evW cs w ≠ 1)) &&
    (!isInv (evW (ctx.gens.take j) w) || (isInv (evW cs w) &&
      decide (blkOf ci ld (evW cs w) = blkOf ci ld (evW (ctx.gens.take j) w)))) &&
    (!isInv (evW (ctx.gens.take j) w * evW (ctx.gens.take j) w) ||
      (isInv (evW cs w * evW cs w) &&
        decide (blkOf ci ld (evW cs w * evW cs w) =
          blkOf ci ld (evW (ctx.gens.take j) w * evW (ctx.gens.take j) w))))

@[expose] def homGo (ctx : HomCtx n) (ci : Array Nat) (ld : List Nat) (cands : List (Idx n)) :
    Nat → Nat → List (Idx n) → Bool
  | 0, j, cs => candOK ctx ci ld j cs
  | d + 1, j, cs =>
    candOK ctx ci ld j cs && cands.any fun c => homGo ctx ci ld cands d (j + 1) (cs ++ [c])

@[expose] def homExists (ctx : HomCtx n) (ci : Array Nat) (ld : List Nat) (tp : Idx n) : Bool :=
  homGo ctx ci ld ((elemsI n).filter fun c => decide (c * tp = tp * c)) (ctx.gens.length - 1) 1
    [tp]

@[expose] def scpOK (e : Eng n) (ld : List Nat) : Bool :=
  (List.range e.reps.length).all fun k =>
    homExists (e.ctxs.getD k default) e.ciA ld (tpOf e ld (ld.getD k 0))

@[expose] def feasible (e : Eng n) (ld : List Nat) : Bool :=
  xOK e ld && thompsonOK e ld && scpOK e ld

@[expose] def leaders : Nat → List (List Nat)
  | 0 => [[]]
  | m + 1 => (leaders m).flatMap fun l =>
      ((List.range (m + 1)).filter fun j => decide (j = m) || decide (l.getD j 0 = j)).map
        fun j => l ++ [j]

@[expose] def survivors (e : Eng n) : List (List Nat) :=
  (leaders e.reps.length).filter (feasible e)

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
