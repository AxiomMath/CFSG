module

public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

namespace CFSG.KC.Benes

open CFSG.KC.Load

meta def kNat (what : String) (e : Expr) : CoreM Nat := do
  match Kernel.whnf (← getEnv) {} e with
  | .ok (.lit (.natVal v)) => return v
  | .ok r => throwError "{what}: no literal, got {r.getAppFn}"
  | .error ex => throwKernelException ex

meta partial def bytesLE (x n : Nat) : ByteArray :=
  if n ≤ 8 then ⟨(Array.range n).map fun i => ((x >>> (8 * i)) &&& 255).toUInt8⟩
  else
    let h := n / 2
    bytesLE (x &&& ((1 <<< (8 * h)) - 1)) h ++ bytesLE (x >>> (8 * h)) (n - h)

meta def mapOfPlanes (k X : Nat) : Array Nat := Id.run do
  let W := 1 <<< k
  let pb := W / 8
  let b := bytesLE X (k * pb)
  let mut s : Array Nat := Array.replicate W 0
  for pl in [0:k] do
    for q in [0:pb] do
      let y := b[pl * pb + q]!
      if y != 0 then
        for t in [0:8] do
          if (y >>> t.toUInt8) &&& 1 == 1 then
            s := s.modify (8 * q + t) (· ||| (1 <<< pl))
  return s

meta def invPerm? (s : Array Nat) : Option (Array Nat) := Id.run do
  let n := s.size
  let mut inv : Array Nat := Array.replicate n n
  for p in [0:n] do
    let v := s[p]!
    if v ≥ n || inv[v]! != n then return none
    inv := inv.set! v p
  return some inv

meta def setBitB (b : ByteArray) (p : Nat) : ByteArray :=
  b.set! (p >>> 3) (b.get! (p >>> 3) ||| ((1 : UInt8) <<< (p &&& 7).toUInt8))

meta def route (m : Nat) (dst : Array Nat) : Array ByteArray := Id.run do
  let W := 1 <<< m
  let zero : ByteArray := ⟨Array.replicate ((W + 7) / 8) 0⟩
  let mut masks : Array ByteArray := Array.replicate (2 * m - 1) zero
  let mut f := dst
  let mut finv : Array Nat := Array.replicate W 0
  for q in [0:W] do
    finv := finv.set! f[q]! q
  for lvl in [0:m - 1] do
    let h := 1 <<< (m - 1 - lvl)
    let lowH := h - 1
    let hiMask := (W - 1) ^^^ (2 * h - 1)
    let mut col : ByteArray := ⟨Array.replicate W 2⟩
    for q0 in [0:W] do
      if col.get! q0 == 2 then
        let mut q := q0
        let mut go := true
        while go do
          col := col.set! q 0
          let q2 := finv[f[q]! ^^^ h]!
          col := col.set! q2 1
          let q3 := q2 ^^^ h
          if col.get! q3 == 2 then q := q3 else go := false
    let mut mi := masks[lvl]!
    let mut mo := masks[2 * m - 2 - lvl]!
    masks := masks.set! lvl zero
    masks := masks.set! (2 * m - 2 - lvl) zero
    let mut nf : Array Nat := Array.replicate W 0
    let mut nfi : Array Nat := Array.replicate W 0
    for q in [0:W] do
      let c := col.get! q
      if q &&& h == 0 then
        if c == 1 then mi := setBitB mi q
        if col.get! finv[q]! == 1 then mo := setBitB mo q
      let base := (q &&& hiMask) + (if c == 1 then h else 0)
      let p := base + (q &&& lowH)
      let d := base + (f[q]! &&& lowH)
      nf := nf.set! p d
      nfi := nfi.set! d p
    masks := masks.set! lvl mi
    masks := masks.set! (2 * m - 2 - lvl) mo
    f := nf
    finv := nfi
  let mut mid := masks[m - 1]!
  masks := masks.set! (m - 1) zero
  for p in [0:W / 2] do
    if f[2 * p]! != 2 * p then mid := setBitB mid (2 * p)
  masks := masks.set! (m - 1) mid
  return masks

meta def netOfPlanes (what : String) (k X : Nat) : CoreM Nat := do
  let s := mapOfPlanes k X
  let some inv := invPerm? s | throwError "{what}: not the plane form of a permutation"
  let masks := route k inv
  let W := 1 <<< k
  let mut N := 0
  for (mk, i) in masks.zipIdx do
    N := N ||| (natLE mk 0 mk.size <<< (i * W))
  return N

meta def prefixFn (names : Array Name) : Expr :=
  let motive := mkLambda `x .default boolE natE
  let body := names.zipIdx.foldr (fun (n, c) acc =>
    mkApp4 (mkConst ``Bool.rec [1]) motive acc (mkConst n)
      (mkApp2 (mkConst ``Nat.beq) (.bvar 0) (mkRawNatLit c))) (mkRawNatLit 0)
  mkLambda `j .default natE body

end CFSG.KC.Benes

open CFSG.KC.Load CFSG.KC.Benes in
elab "#kc_benes " pre:ident base:ident start:num count:num k:num f:term : command => do
  let ty := mkForall `T .default fnT (mkForall `j .default natE natE)
  let fe ← liftTermElabM do
    let e ← Term.elabTermEnsuringType f (some ty)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar then throwError "#kc_benes: the term has metavariables"
    pure e
  let B := pre.getId ++ base.getId
  let (start, count, k) := (start.getNat, count.getNat, k.getNat)
  unless 3 ≤ k do throwError "#kc_benes: k must be at least 3"
  withSync do
    for j in [start:start + count] do
      let names := (Array.range j).map fun c => B.appendAfter s!"{c}"
      let X ← kNat s!"{B}{j}" (mkApp2 fe (prefixFn names) (mkRawNatLit j))
      let N ← netOfPlanes s!"{B}{j}" k X
      addDef (B.appendAfter s!"{j}") natE (mkRawNatLit N) true
