module

public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

namespace CFSG.KC.F2Bfs

open CFSG.KC.Load

meta def kwhnf (e : Expr) : CoreM Expr := do
  match Kernel.whnf (← getEnv) {} e with
  | .ok r => return r
  | .error ex => throwKernelException ex

meta partial def natList (e : Expr) : CoreM (Array Nat) := do
  let e ← kwhnf e
  if e.isAppOfArity ``List.cons 3 then
    let h ← kwhnf (e.getArg! 1)
    let some v := h.rawNatLit? | throwError "#kc_f2bfs: a generator is not a literal: {h}"
    return #[v] ++ (← natList (e.getArg! 2))
  else if e.isAppOfArity ``List.nil 1 then return #[]
  else throwError "#kc_f2bfs: not a list: {e}"

meta def mulP (d lw m X Y : Nat) : Nat := Id.run do
  let mut acc := 0
  for c in [0:d] do
    acc := acc ^^^ (((X >>> c) &&& lw) * ((Y >>> (d * c)) &&& m))
  return acc

meta def search (d cap : Nat) (G : Array Nat) : Array Nat × Array (Array Nat) × Array Nat :=
  Id.run do
    let lw := (List.range d).foldl (fun a i => a ||| (1 <<< (d * i))) 0
    let m := (1 <<< d) - 1
    let one := (List.range d).foldl (fun a i => a ||| (1 <<< (d * i + i))) 0
    let mut el : Array Nat := #[one]
    let mut pos : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert one 0
    let mut tbl : Array (Array Nat) := #[]
    let mut cnt : Array Nat := #[]
    for h in [0:cap] do
      if h < el.size then
        cnt := cnt.push el.size
        let x := el[h]!
        let mut row : Array Nat := #[]
        for g in G do
          let y := mulP d lw m x g
          match pos.get? y with
          | some i => row := row.push i
          | none =>
            pos := pos.insert y el.size
            row := row.push el.size
            el := el.push y
        tbl := tbl.push row
    return (el, tbl, cnt)

end CFSG.KC.F2Bfs

open CFSG.KC.F2Bfs CFSG.KC.Load in
elab "#kc_f2bfs " pre:ident dN:num gens:ident capN:num lbN:num wN:num : command => do
  let d := dN.getNat
  let lb := lbN.getNat
  let w := wN.getNat
  let g ← liftCoreM <| realizeGlobalConstNoOverload gens
  let G ← liftCoreM <| natList (mkConst g)
  let (el, tbl, cnt) := search d capN.getNat G
  let n := el.size
  unless tbl.size == n do throwError "#kc_f2bfs: {tbl.size} rows processed, {n} entries"
  unless n < 2 ^ w do throwError "#kc_f2bfs: {n} entries do not fit in {w} bits"
  let srt := ((Array.range n).qsort fun a b => el[a]! < el[b]!)
  let ng := G.size
  let dd := d * d
  let rw := dd + (ng + 2) * w
  let rec_ := fun k => Id.run do
    let mut r := el[k]!
    for j in [0:ng] do
      r := r ||| ((tbl[k]!)[j]! <<< (dd + w * j))
    r := r ||| (cnt[k]! <<< (dd + w * ng))
    r ||| (srt[k]! <<< (dd + w * (ng + 1)))
  let B := 1 <<< lb
  let nc := (n + B - 1) / B
  let P := pre.getId
  withSync do
    addDef (P ++ `N) natE (mkRawNatLit n) true
    for c in [0:nc] do
      let mut v := 0
      for i in [0:B] do
        let k := c * B + i
        if k < n then v := v ||| (rec_ k <<< (rw * i))
      addDef (P ++ Name.mkSimple s!"C{c}") natE (mkRawNatLit v) true
    let dsel := max 1 (Nat.log2 (2 * nc - 1))
    let F := P ++ `CF
    let leaf := fun k => if k < nc then mkConst (P ++ Name.mkSimple s!"C{k}") else mkRawNatLit 0
    CFSG.KC.Load.addSel F leaf 0 (1 <<< dsel) (dsel - 1)
    addDef F CFSG.KC.Load.fnT
      (mkLambda `k .default natE (mkApp (mkConst (F.appendAfter s!"_0_{dsel - 1}")) (.bvar 0))) true
