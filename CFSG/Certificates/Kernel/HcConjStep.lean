module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Std.Data.HashMap
public import CFSG.Certificates.Kernel.Common.Eval

namespace CFSG.KC.HcPack.ConjStep

open CFSG.KC.Eval

meta def mulM (x g : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:32] do
    let gi := (g >>> (5 * i)) % 32
    r := r + (((x >>> (5 * gi)) % 32) <<< (5 * i))
  return r

meta def invM (x : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:32] do
    let xi := (x >>> (5 * i)) % 32
    r := r + (i <<< (5 * xi))
  return r

meta def nats (v : Val) : Except String (Array Nat) :=
  match v with
  | .list xs => xs.mapM fun
    | .nat n => .ok n
    | _ => .error "expected a list of numbers"
  | _ => .error "expected a list"

meta def posMap (xs : Array Nat) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for i in [0:xs.size] do
    m := m.insert xs[i]! i
  return m

meta def natL (xs : Array Nat) : Val := .list (xs.map .nat)

public meta def cjRec (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (EV, RV, gsV, IV) ← match args with
    | #[EV, RV, gsV, IV] => pure (EV, RV, gsV, IV)
    | _ => throw "expected elements, representatives, letters and classes"
  let E ← nats EV
  let R ← nats RV
  let gs ← nats gsV
  let I ← nats IV
  if gs.size != 10 then throw "expected ten letters"
  let idP := (List.range 32).foldr (fun a acc => a + 32 * acc) 0
  let prs : Array (Nat × Nat) := (Array.range 5).foldl
    (fun acc k => (acc.push (gs[k]!, gs[k + 5]!)).push (gs[k + 5]!, gs[k]!)) #[]
  let posE := posMap E
  let mut KF : Array (Array Nat) := #[]
  let mut KS : Array (Array Nat) := #[]
  for r in R do
    let mut f : Array Nat := #[r]
    let mut s : Array Nat := #[idP]
    let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert r 0
    let mut fr : Array (Nat × Nat) := #[(r, idP)]
    let mut rounds := 0
    while !fr.isEmpty do
      rounds := rounds + 1
      if rounds > 100 then throw "more than 100 rounds"
      let mut nf : Array (Nat × Nat) := #[]
      for p in fr do
        for (a, b) in prs do
          let x' := mulM (mulM a p.1) b
          if !idx.contains x' then
            let c' := mulM a p.2
            idx := idx.insert x' f.size
            f := f.push x'
            s := s.push c'
            nf := nf.push (x', c')
      fr := nf
    KF := KF.push f
    KS := KS.push s
  let mut dC : Array Val := #[]
  let mut pF : Array Val := #[]
  let mut pS : Array Val := #[]
  for j in [0:KF.size] do
    let f := KF[j]!
    let pm := posMap f
    let mut d : Array Nat := #[]
    for x in f do
      for (a, b) in prs do
        match pm[mulM (mulM a x) b]? with
        | some t => d := d.push t
        | none => throw "a class is not closed"
    dC := dC.push (natL d)
    pF := pF.push (natL (← f.mapM fun x => match posE[x]? with
      | some t => pure t | none => throw "an entry is not in E"))
    pS := pS.push (natL (← KS[j]!.mapM fun x => match posE[x]? with
      | some t => pure t | none => throw "a conjugator is not in E"))
  let L : Array Nat := KF.foldl (· ++ ·) #[]
  let oL := (Array.range L.size).qsort fun i j => L[i]! < L[j]!
  let posL := posMap L
  let pL ← E.mapM fun x => match posL[x]? with
    | some t => pure t | none => throw "an element is in no class"
  let pI ← E.mapM fun x => match posE[invM x]? with
    | some t => pure t | none => throw "an inverse is not in E"
  let cls : Std.HashMap Nat (Nat × Nat) := Id.run do
    let mut m : Std.HashMap Nat (Nat × Nat) := {}
    for j in [0:KF.size] do
      for t in [0:KF[j]!.size] do
        m := m.insert KF[j]![t]! (j, t)
    return m
  let mut aC : Array Val := #[]
  let mut aT : Array Val := #[]
  for r in I do
    let mut rc : Array Val := #[]
    let mut rt : Array Val := #[]
    for k in [0:R.size] do
      let mut cs : Array Nat := #[]
      let mut ts : Array Nat := #[]
      for x in KF[r]! do
        match cls[mulM (invM x) R[k]!]? with
        | some (c, t) => cs := cs.push c; ts := ts.push t
        | none => throw "a product is in no class"
      rc := rc.push (natL cs)
      rt := rt.push (natL ts)
    aC := aC.push (.list rc)
    aT := aT.push (.list rt)
  return #[(`KF, .list (KF.map natL)), (`KS, .list (KS.map natL)), (`dC, .list dC),
    (`pF, .list pF), (`pS, .list pS), (`oL, natL oL), (`pL, natL pL), (`pI, natL pI),
    (`aC, .list aC), (`aT, .list aT)]

end CFSG.KC.HcPack.ConjStep
