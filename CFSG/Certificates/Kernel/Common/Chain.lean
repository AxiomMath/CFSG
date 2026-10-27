module

public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.Benes
meta import all CFSG.Certificates.Kernel.Common.Benes
public import CFSG.Certificates.Kernel.Common.Benes

open Lean Elab Command

namespace CFSG.KC.Chain

open CFSG.KC.Load

meta def readRepoPinned (rel : String) (size hash : Nat) : CommandElabM ByteArray := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let path := dir / rel
  let b ← IO.FS.readBinFile path
  let h := b.hash.toNat
  unless b.size == size && h == hash do
    throwError "plan file {path}: size {b.size} hash {h}, pinned size {size} hash {hash}"
  return b

meta def fld20 (c k : Nat) : Nat := (c >>> (20 * k)) &&& 1048575

meta def natValOf (n : Name) : CoreM Nat := do
  match (← getConstInfo n).value? with
  | some (.lit (.natVal v)) => return v
  | _ => throwError "{n} is not a natural number literal"

meta def kwhnf (e : Expr) : CoreM Expr := do
  match Kernel.whnf (← getEnv) {} e with
  | .ok r => return r
  | .error ex => throwKernelException ex

meta def kNat (what : String) (e : Expr) : CoreM Nat := do
  match ← kwhnf e with
  | .lit (.natVal v) => return v
  | r => throwError "{what}: no literal, got {r}"

meta def kPair (what : String) (e : Expr) : CoreM (Expr × Expr) := do
  let r ← kwhnf e
  if r.isAppOfArity ``Prod.mk 4 then return (r.getArg! 2, r.getArg! 3)
  throwError "{what}: no pair, got {r.getAppFn}"

meta def evalSt (what : String) (e : Expr) : CoreM (Nat × Nat × Nat) := do
  let (f, r) ← kPair what e
  unless (← kwhnf f).isConstOf ``Bool.true do throwError "{what}: the flag is not true"
  let (x, r2) ← kPair what r
  let (a, w) ← kPair what r2
  return (← kNat what x, ← kNat what a, ← kNat what w)

meta def stOf (X A W : Expr) : Expr :=
  let nn := mkApp2 (mkConst ``Prod [0, 0]) natE natE
  let nnn := mkApp2 (mkConst ``Prod [0, 0]) natE nn
  mkApp4 (mkConst ``Prod.mk [0, 0]) boolE nnn (mkConst ``Bool.true)
    (mkApp4 (mkConst ``Prod.mk [0, 0]) natE nn X (mkApp4 (mkConst ``Prod.mk [0, 0]) natE natE A W))

meta partial def natWords (x nw : Nat) : Array UInt64 :=
  if nw ≤ 1 then #[x.toUInt64]
  else
    let h := nw / 2
    natWords (x % (1 <<< (64 * h))) h ++ natWords (x >>> (64 * h)) (nw - h)

meta def labelsOf (S n x : Nat) : Array Nat := Id.run do
  let nwp := S / 64
  let w := natWords x (n * nwp)
  let mut lab : Array Nat := Array.replicate S 0
  for b in [0:n] do
    for k in [0:nwp] do
      let mut v := w[b * nwp + k]!
      while v != 0 do
        let t := v.toNat.log2
        lab := lab.modify (64 * k + t) (· ||| (1 <<< b))
        v := v ^^^ ((1 : UInt64) <<< t.toUInt64)
  return lab

meta def matchPerm (src tgt : Array Nat) : Except String (Array Nat) := Id.run do
  let n := src.size
  let ks := ((Array.range n).map fun u => (src[u]! <<< 20) ||| u).qsort (· < ·)
  let kt := ((Array.range n).map fun p => (tgt[p]! <<< 20) ||| p).qsort (· < ·)
  let mut sig : Array Nat := Array.replicate n 0
  for i in [0:n] do
    if ks[i]! >>> 20 != kt[i]! >>> 20 then
      return .error s!"the labels differ (rank {i}: source position {ks[i]! &&& 1048575})"
    sig := sig.set! (ks[i]! &&& 1048575) (kt[i]! &&& 1048575)
  return .ok sig

meta def addRoute (name : Name) (k n : Nat) (src tgt : Expr) : CoreM Unit := do
  unless 6 ≤ k && k ≤ 20 do throwError "{name}: 2^{k} positions, outside 2^6 … 2^20"
  let S := 1 <<< k
  let ls := labelsOf S n (← kNat s!"{name} source" src)
  let lt := labelsOf S n (← kNat s!"{name} target" tgt)
  match matchPerm ls lt with
  | .error e => throwError "{name}: {e}"
  | .ok sig =>
    let mut N := 0
    for (mk, i) in (CFSG.KC.Benes.route k sig).zipIdx do
      N := N ||| (natLE mk 0 mk.size <<< (i * S))
    addDef name natE (mkRawNatLit N) true

meta partial def parseTerms (pre : Name) (b : ByteArray) (i stop : Nat) (acc : Array Expr) :
    Except String (Array Expr) := do
  let i := skipWs b i stop
  if i ≥ stop then return acc
  let (t, j) ← parseTerm pre b i stop
  parseTerms pre b j stop (acc.push t)

meta def addComputed (pre : Name) (kind : UInt8) (b : ByteArray) (lo hi : Nat) : CoreM Unit := do
  let ns := skipWs b (lo + 1) hi
  let ne := tokEnd b ns hi
  let name := tokName pre b ns ne
  let ts ← match parseTerms pre b ne hi #[] with
    | .ok ts => pure ts
    | .error msg => throwError "line {name}: {msg}"
  if kind == 69 then
    unless ts.size == 1 do throwError "line {name}: E takes one term"
    addDef name natE (mkRawNatLit (← kNat s!"{name}" ts[0]!)) true
  else
    unless ts.size == 4 do throwError "line {name}: R takes k, n, source, target"
    addRoute name (← kNat s!"{name}" ts[0]!) (← kNat s!"{name}" ts[1]!) ts[2]! ts[3]!

meta def loadPlan (pre : Name) (b : ByteArray) : CoreM (Array Expr) := do
  let mut wit : Array Expr := #[]
  let mut lo := 0
  for i in [0:b.size + 1] do
    if i == b.size || b[i]! == 10 then
      let s := skipWs b lo i
      if s + 1 < i && b[s + 1]! == 32 && (b[s]! == 69 || b[s]! == 82) then
        addComputed pre b[s]! b s i
      else if s + 1 < i && b[s]! == 83 && b[s + 1]! == 32 then
        match parseTerm pre b (s + 1) i with
        | .ok (t, _) => wit := wit.push t
        | .error msg => throwError "S line {wit.size}: {msg}"
      else if lo < i then addLine pre false b lo i
      lo := i + 1
  return wit

meta def addChain (pre : Name) (run : Option Name) (wit : Array Expr) : CoreM Unit := do
  let w := wit.size
  let mut st : Std.HashMap Nat Expr := {}
  for (t, i) in wit.zipIdx do
    st := st.insert i t
  let mut k : Nat := 0
  let mut nx : Nat := 0
  while (← getEnv).contains (pre ++ Name.mkSimple s!"CH{k}") do
    let some run := run | throwError "the plan has chunks and no run is given"
    let c ← natValOf (pre ++ Name.mkSimple s!"CH{k}")
    let (σ, i, j) := (fld20 c 0, fld20 c 3, fld20 c 4)
    if fld20 c 5 == 0 && j ≥ w && !st.contains j then
      let some s := st[i]? | throwError "chunk {k}: no state {i} before it"
      unless j == w + nx do throwError "chunk {k}: state {j} out of order (next is {w + nx})"
      let wd := pre ++ Name.mkSimple s!"wd{σ}"
      let wdE := if (← getEnv).contains wd then mkConst wd else mkRawNatLit σ
      let e := mkApp3 (mkConst run) wdE (mkRawNatLit c) s
      let (x, a, ww) ← evalSt s!"chunk {k}" e
      let names := #["X", "A", "W"].map fun p => pre ++ Name.mkSimple s!"{p}{nx}"
      addDef names[0]! natE (mkRawNatLit x) true
      addDef names[1]! natE (mkRawNatLit a) true
      addDef names[2]! natE (mkRawNatLit ww) true
      st := st.insert j (stOf (mkConst names[0]!) (mkConst names[1]!) (mkConst names[2]!))
      nx := nx + 1
    k := k + 1

end CFSG.KC.Chain

open CFSG.KC.Chain CFSG.KC.Load in
elab "#kc_chain " pre:ident run:(ident)? path:str size:num hash:num : command => do
  let b ← readRepoPinned path.getString size.getNat hash.getNat
  let run ← run.mapM fun r => liftCoreM <| realizeGlobalConstNoOverload r
  withSync do
    let wit ← loadPlan pre.getId b
    addChain pre.getId run wit
