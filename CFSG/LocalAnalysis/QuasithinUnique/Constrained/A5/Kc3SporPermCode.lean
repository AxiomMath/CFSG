module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporPerm

open CFSG.QuasithinUnique.K1.SporadicPerm

structure PD where
  n : Nat
  B : List Nat
  G : List (Array Nat)
  Gi : List (Array Nat)
  Ts : Array (List Nat)
  par : Array Nat
  cl : Array Nat

@[expose] def PD.L (D : PD) : Array (Array Nat) := (D.G ++ D.Gi).toArray

@[expose] def evalPt (L : Array (Array Nat)) : List Nat → Nat → Nat
  | [], p => p
  | l :: w, p => img L[l]! (evalPt L w p)

@[expose] def applyW (L : Array (Array Nat)) (w : List Nat) (T : List Nat) : List Nat :=
  T.map (evalPt L w)

@[expose] def letterOf (G : List (Array Nat)) (Ts : Array (List Nat)) (par : Array Nat)
    (i : Nat) : Nat :=
  G.findIdx fun s => applyTab s Ts[par[i]!]! == Ts[i]!

@[expose] def mkWd (G : List (Array Nat)) (Ts : Array (List Nat)) (par : Array Nat) :
    Array (List Nat) :=
  (List.range Ts.size).foldl (fun acc i =>
    acc.push (if i = 0 then [] else letterOf G Ts par i :: acc[par[i]!]!)) #[]

@[expose] def WdOK (G : List (Array Nat)) (Ts : Array (List Nat)) (par : Array Nat)
    (wd : Array (List Nat)) : Prop :=
  wd.size = Ts.size ∧ wd[0]! = [] ∧
    ∀ i < Ts.size, 0 < i → ∃ l < G.length, wd[i]! = l :: wd[par[i]!]! ∧
      Ts[i]! = applyTab G[l]! Ts[par[i]!]!

instance (G : List (Array Nat)) (Ts : Array (List Nat)) (par : Array Nat)
    (wd : Array (List Nat)) : Decidable (WdOK G Ts par wd) := by
  unfold WdOK; infer_instance

@[expose] def isInv (r : Nat) (L : Array (Array Nat)) (wd : Array (List Nat))
    (Ts : Array (List Nat)) (i : Nat) : Bool :=
  applyW L wd[i]! (Ts[i]!.take r) == (Ts[0]!).take r

@[expose] def mkIv (r : Nat) (L : Array (Array Nat)) (wd : Array (List Nat))
    (Ts : Array (List Nat)) : Array Nat :=
  ((List.range Ts.size).filter fun i => 0 < i && isInv r L wd Ts i).toArray

@[expose] def mkIvMap (n r : Nat) (Ts : Array (List Nat)) (iv : Array Nat) :
    Std.HashMap Nat Nat :=
  (List.range iv.size).foldl (fun m k => m.insert (keyNat n r Ts[iv[k]!]!) k) {}

@[expose] def MapOK (n r : Nat) (Ts : Array (List Nat)) (iv : Array Nat)
    (ivMap : Std.HashMap Nat Nat) : Prop :=
  ∀ k < iv.size, ivMap[keyNat n r Ts[iv[k]!]!]? = some k

instance (n r : Nat) (Ts : Array (List Nat)) (iv : Array Nat) (ivMap : Std.HashMap Nat Nat) :
    Decidable (MapOK n r Ts iv ivMap) := by
  unfold MapOK; infer_instance

@[expose] def mkFs (n : Nat) (Ts : Array (List Nat)) (iv : Array Nat) : Array Bool :=
  iv.foldl (fun a i => a.set! ((Ts[i]!).headD 0) true) (Array.replicate n false)

@[expose] def FsOK (Ts : Array (List Nat)) (iv : Array Nat) (fs : Array Bool) : Prop :=
  ∀ k < iv.size, fs[(Ts[iv[k]!]!).headD 0]! = true

instance (Ts : Array (List Nat)) (iv : Array Nat) (fs : Array Bool) :
    Decidable (FsOK Ts iv fs) := by
  unfold FsOK; infer_instance

@[expose] def prodF (n r : Nat) (L : Array (Array Nat)) (wd : Array (List Nat))
    (Ts : Array (List Nat)) (iv : Array Nat) (ivMap : Std.HashMap Nat Nat) (fs : Array Bool)
    (M i j : Nat) : Nat :=
  let w := wd[iv[i]!]!
  let T := Ts[iv[j]!]!
  if fs[evalPt L w (T.headD 0)]! then
    let T5 := applyW L w (T.take r)
    match ivMap[keyNat n r T5]? with
    | none => M
    | some k => if T5 == (Ts[iv[k]!]!).take r then k else M
  else M

@[expose] def mkPtab (n r : Nat) (L : Array (Array Nat)) (wd : Array (List Nat))
    (Ts : Array (List Nat)) (iv : Array Nat) (ivMap : Std.HashMap Nat Nat) (fs : Array Bool) :
    Array Nat :=
  let M := iv.size
  (Array.range (M * M)).map fun idx =>
    if idx / M < idx % M then prodF n r L wd Ts iv ivMap fs M (idx / M) (idx % M) else M

@[expose] def prAt (M : Nat) (ptab : Array Nat) (i j : Nat) : Nat :=
  if i < j then ptab[i * M + j]! else if j < i then ptab[j * M + i]! else M

@[expose] def mkNbr (M : Nat) (ptab : Array Nat) : Array (List Nat) :=
  (Array.range M).map fun i => (List.range M).filter fun j => decide (prAt M ptab i j < M)

@[expose] def invL (g l : Nat) : Nat := (l + g) % (2 * g)

@[expose] def invW (g : Nat) (w : List Nat) : List Nat := w.reverse.map (invL g)

@[expose] def conjTabW (L : Array (Array Nat)) (g : Nat) (P : List Nat) (cw wr : List Nat) :
    List Nat :=
  P.map (evalPt L (cw ++ wr ++ invW g cw))

@[expose] def mkConj (n r : Nat) (L : Array (Array Nat)) (g : Nat) (P : List Nat)
    (wd : Array (List Nat)) (iv : Array Nat) (ivMap : Std.HashMap Nat Nat) :
    Array Nat × Array (List Nat) := Id.run do
  let M := iv.size
  let mut rt : Array Nat := Array.range M
  let mut cw : Array (List Nat) := Array.replicate M []
  let mut seen : Array Bool := Array.replicate M false
  for root in [0:M] do
    if !seen[root]! then
      seen := seen.set! root true
      let mut queue : Array Nat := #[root]
      let mut qi := 0
      while qi < queue.size do
        let p := queue[qi]!
        qi := qi + 1
        for l in [0:g] do
          let T := conjTabW L g P (l :: cw[p]!) wd[iv[root]!]!
          match ivMap[keyNat n r T]? with
          | some k =>
            if !seen[k]! then
              seen := seen.set! k true
              rt := rt.set! k root
              cw := cw.set! k (l :: cw[p]!)
              queue := queue.push k
          | none => pure ()
  return (rt, cw)

@[expose] def ConjOK (L : Array (Array Nat)) (g : Nat) (P : List Nat) (wd : Array (List Nat))
    (Ts : Array (List Nat)) (iv : Array Nat) (rt : Array Nat) (cw : Array (List Nat)) : Prop :=
  rt.size = iv.size ∧ cw.size = iv.size ∧
    ∀ k < iv.size, rt[k]! < iv.size ∧ rt[rt[k]!]! = rt[k]! ∧ (∀ l ∈ cw[k]!, l < 2 * g) ∧
      Ts[iv[k]!]! = conjTabW L g P cw[k]! wd[iv[rt[k]!]!]!

instance (L : Array (Array Nat)) (g : Nat) (P : List Nat) (wd : Array (List Nat))
    (Ts : Array (List Nat)) (iv : Array Nat) (rt : Array Nat) (cw : Array (List Nat)) :
    Decidable (ConjOK L g P wd Ts iv rt cw) := by
  unfold ConjOK; infer_instance

@[expose] def mkFxR (n : Nat) (L : Array (Array Nat)) (wd : Array (List Nat)) (iv : Array Nat)
    (rt : Array Nat) : Array (List Nat) :=
  (Array.range iv.size).map fun k =>
    if rt[k]! == k then
      let w := wd[iv[k]!]!
      (List.range n).filter fun p => evalPt L w p == p
    else []

@[expose] def mkFx (L : Array (Array Nat)) (rt : Array Nat) (cw : Array (List Nat))
    (fxr : Array (List Nat)) : Array (List Nat) :=
  (Array.range rt.size).map fun k => (fxr[rt[k]!]!).map (evalPt L cw[k]!)

@[expose] def mkMem (n : Nat) (fx : Array (List Nat)) : Array (Array Bool) :=
  fx.map fun l => l.foldl (fun a p => a.set! p true) (Array.replicate n false)

@[expose] def mkCtab (M : Nat) (fx : Array (List Nat)) (mem : Array (Array Bool))
    (ptab : Array Nat) : Array Nat :=
  (Array.range (M * M)).map fun idx =>
    if idx / M < idx % M && ptab[idx]! < M then
      (fx[idx / M]!).countP (fun p => (mem[idx % M]!)[p]!)
    else 0

@[expose] def ctAt (M : Nat) (ctab : Array Nat) (i j : Nat) : Nat :=
  if i < j then ctab[i * M + j]! else if j < i then ctab[j * M + i]! else 0

@[expose] def pairsL : List (Nat × Nat) :=
  ((List.range 16).flatMap fun a => (List.range 16).map fun b => (a, b)).filter
    fun p => 0 < p.1 && 0 < p.2 && p.1 != p.2

@[expose] def okSize (c : Nat) : Bool :=
  c == 0 || c == 60 || c == 90 || c == 120 || c == 150 || c == 210

@[expose] def witness (vals : List Nat) : Nat :=
  let mx := vals.foldl max 0
  let h := vals.foldl (fun (h : Array Nat) v => h.modify v (· + 1)) (Array.replicate (mx + 1) 0)
  (vals.find? fun v => !okSize h[v]!).getD 0

@[expose] def elF (pr : Nat → Nat → Nat) (i j k l a : Nat) : Nat :=
  match a with
  | 1 => i
  | 2 => j
  | 3 => pr i j
  | 4 => k
  | 5 => pr i k
  | 6 => pr j k
  | 7 => pr (pr i j) k
  | 8 => l
  | 9 => pr i l
  | 10 => pr j l
  | 11 => pr (pr i j) l
  | 12 => pr k l
  | 13 => pr (pr i k) l
  | 14 => pr (pr j k) l
  | 15 => pr (pr (pr i j) k) l
  | _ => 0

@[expose] def leafBad (pr ct : Nat → Nat → Nat) (i j k l : Nat) : Bool :=
  let el := ((List.range 16).map (elF pr i j k l)).toArray
  let vals := pairsL.map fun p => ct el[p.1]! el[p.2]!
  !(okSize (vals.count (witness vals)))

@[expose] def g2 (M : Nat) (pr : Nat → Nat → Nat) (i j : Nat) : Bool :=
  decide (i < j) && decide (pr i j < M) && decide (j < pr i j)

@[expose] def g3 (M : Nat) (pr : Nat → Nat → Nat) (i j k : Nat) : Bool :=
  decide (j < k) && decide (pr i k < M) && decide (pr j k < M) && decide (pr (pr i j) k < M) &&
    decide (k < pr i k) && decide (k < pr j k) && decide (k < pr (pr i j) k)

@[expose] def g4 (M : Nat) (pr : Nat → Nat → Nat) (i j k l : Nat) : Bool :=
  decide (k < l) && decide (pr i l < M) && decide (pr j l < M) && decide (pr (pr i j) l < M) &&
    decide (pr k l < M) && decide (pr (pr i k) l < M) && decide (pr (pr j k) l < M) &&
    decide (pr (pr (pr i j) k) l < M) && decide (l < pr i l) && decide (l < pr j l) &&
    decide (l < pr (pr i j) l) && decide (l < pr k l) && decide (l < pr (pr i k) l) &&
    decide (l < pr (pr j k) l) && decide (l < pr (pr (pr i j) k) l)

@[expose] def dfsB (M : Nat) (pr ct : Nat → Nat → Nat) (nbr : Nat → List Nat) : Bool :=
  (List.range M).all fun i =>
    (nbr i).all fun j =>
      !(g2 M pr i j) ||
        (nbr i).all fun k =>
          !(g3 M pr i j k) ||
            (nbr i).all fun l =>
              !(g4 M pr i j k l) || leafBad pr ct i j k l

end CFSG.QuasithinUnique.A5.Kc3SporPerm
