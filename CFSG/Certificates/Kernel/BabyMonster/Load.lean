module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.DataRoot
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KC.BM.Load

meta def N : Nat := 4370

meta partial def natLE (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 8 then
    Id.run do
      let mut acc := 0
      for k in [0:hi - lo] do
        acc := acc + (b[lo + k]!.toNat <<< (8 * k))
      return acc
  else
    let mid := lo + (hi - lo) / 2
    natLE b lo mid + (natLE b mid hi <<< (8 * (mid - lo)))

meta def dataRoot {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m] : m System.FilePath :=
  CFSG.KC.dataRoot

meta def readPinned {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m]
    (rel : String) (size hash : Nat) : m ByteArray := do
  let path := (← dataRoot) / rel
  monadLift (m := IO) do
  let b ← IO.FS.readBinFile path
  unless b.size == size && b.hash.toNat == hash do
    throw (IO.userError s!"data file {path}: size {b.size} hash {b.hash.toNat}, pinned {size} {hash}")
  return b

@[inline] meta def fbit (b : ByteArray) (k j : Nat) : Bool :=
  (b[552 * k + j / 8]! >>> (j % 8).toUInt8) &&& 1 == 1

meta def checkMatrixFile (b : ByteArray) (rows : Nat) : IO Unit := do
  unless b.size == rows * 552 do throw (IO.userError s!"matrix file of size {b.size}")
  for k in [0:rows] do
    for j in [N:552 * 8] do
      if fbit b k j then throw (IO.userError s!"row {k} has bit {j} past column {N}")

meta def natE : Expr := mkConst ``Nat
meta def boolE : Expr := mkConst ``Bool
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE

meta def mkList (ty : Expr) (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) ty e acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

meta def addTrueThm (name : Name) (b : Expr) : CoreM Float := do
  let t0 ← IO.monoNanosNow
  CFSG.KC.addThmDecl <|
    { name, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) boolE b (mkConst ``Bool.true),
      value := reflBoolTrue }
  return ((← IO.monoNanosNow) - t0).toFloat / 1e6

meta def withSync (x : CoreM Unit) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) x

meta def rel (P : Name) (n : Name) : Name :=
  let r := n.getRoot
  if r == `CFSG || r == `Nat || r == `Bool || r == `List then n else P ++ n

meta def stripE (P M : Name) (j : Nat) : Expr :=
  if M == `I then mkApp (mkConst `CFSG.KC.BM.idS) (mkRawNatLit j)
  else mkConst (rel P M ++ Name.mkSimple s!"s{j}")

meta def wordE (P : Name) (ws : Array Name) : Expr :=
  mkApp (mkConst `CFSG.KC.BM.mulW) (mkList listNatE (ws.map fun w => mkConst (rel P w)))

end CFSG.KC.BM.Load

open CFSG.KC.BM.Load

elab "#bm_mat " pre:ident id:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  unless b.size == 69 * 8 * N do throwError "strip file of size {b.size}"
  let M := pre.getId ++ id.getId
  withSync do
    let mut cs : Array Expr := #[]
    for s in [0:69] do
      let nm := M ++ Name.mkSimple s!"s{s}"
      addDef nm natE (mkRawNatLit (natLE b (8 * N * s) (8 * N * (s + 1))))
      cs := cs.push (mkConst nm)
    addDef M listNatE (mkList natE cs)

elab "#bm_rows " pre:ident id:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  checkMatrixFile b N
  let M := pre.getId ++ id.getId
  withSync do
    let mut bs : Array Expr := #[]
    for s in [0:69] do
      let nm := M ++ Name.mkSimple s!"rb{s}"
      let rows := (Array.range (min 64 (N - 64 * s))).map fun t =>
        mkRawNatLit (natLE b (552 * (64 * s + t)) (552 * (64 * s + t + 1)))
      addDef nm listNatE (mkList natE rows)
      bs := bs.push (mkConst nm)
    addDef (M ++ `rows) (mkApp (mkConst ``List [0]) listNatE) (mkList listNatE bs)

elab "#bm_text " pre:ident id:ident path:str size:num hash:num : command => do
  let path := path.getString
  let b ← IO.FS.readBinFile path
  unless b.size == size.getNat && b.hash.toNat == hash.getNat do
    throwError "text file {path}: size {b.size} hash {b.hash.toNat}, pinned {size.getNat} {hash.getNat}"
  unless b.size == 21 + 4425 * N do throwError "text file of size {b.size}"
  let M := pre.getId ++ id.getId
  withSync do
    addDef (M ++ `hdr) natE (mkRawNatLit (natLE b 0 21))
    let mut cs : Array Expr := #[]
    for s in [0:69] do
      let nm := M ++ Name.mkSimple s!"t{s}"
      addDef nm natE (mkRawNatLit (natLE b (21 + 4425 * 64 * s) (21 + 4425 * min N (64 * (s + 1)))))
      cs := cs.push (mkConst nm)
    addDef (M ++ `text) listNatE (mkList natE cs)

elab "#bm_strip " pre:ident id:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  unless b.size == 8 * N do throwError "strip file of size {b.size}"
  withSync <| addDef (pre.getId ++ id.getId) natE (mkRawNatLit (natLE b 0 b.size))

elab "#bm_vec " pre:ident id:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  checkMatrixFile b 1
  withSync <| addDef (pre.getId ++ id.getId) natE (mkRawNatLit (natLE b 0 552))

elab "#bm_matn " pre:ident id:ident n:num path:str size:num hash:num : command => do
  let n := n.getNat
  unless 4352 < n && n ≤ 4416 do throwError "dimension {n} outside the 69-strip range"
  let b ← readPinned path.getString size.getNat hash.getNat
  unless b.size == 69 * 8 * n do throwError "strip file of size {b.size}"
  let M := pre.getId ++ id.getId
  withSync do
    let mut cs : Array Expr := #[]
    for s in [0:69] do
      let nm := M ++ Name.mkSimple s!"s{s}"
      addDef nm natE (mkRawNatLit (natLE b (8 * n * s) (8 * n * (s + 1))))
      cs := cs.push (mkConst nm)
    addDef M listNatE (mkList natE cs)

elab "#bm_rowsn " pre:ident id:ident n:num path:str size:num hash:num : command => do
  let n := n.getNat
  unless 4352 < n && n ≤ 4416 do throwError "dimension {n} outside the 69-strip range"
  let b ← readPinned path.getString size.getNat hash.getNat
  checkMatrixFile b n
  let M := pre.getId ++ id.getId
  withSync do
    let mut bs : Array Expr := #[]
    for s in [0:69] do
      let nm := M ++ Name.mkSimple s!"rb{s}"
      let rows := (Array.range (min 64 (n - 64 * s))).map fun t =>
        mkRawNatLit (natLE b (552 * (64 * s + t)) (552 * (64 * s + t + 1)))
      addDef nm listNatE (mkList natE rows)
      bs := bs.push (mkConst nm)
    addDef (M ++ `rows) (mkApp (mkConst ``List [0]) listNatE) (mkList listNatE bs)

elab "#bm_vecn " pre:ident id:ident n:num path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  unless b.size == 552 do throwError "vector file of size {b.size}"
  for j in [n.getNat:552 * 8] do
    if fbit b 0 j then throwError "bit {j} past column {n.getNat}"
  withSync <| addDef (pre.getId ++ id.getId) natE (mkRawNatLit (natLE b 0 552))

elab "#bm_muln " pre:ident n:num tag:ident a:ident "[" bs:ident* "]" c:ident "[" ds:ident* "]" : command => do
  let P := pre.getId
  let nE := mkRawNatLit n.getNat
  let strip (M : Name) (j : Nat) : Expr :=
    if M == `I then mkApp2 (mkConst `CFSG.KC.BM.idSn) nE (mkRawNatLit j)
    else mkConst (rel P M ++ Name.mkSimple s!"s{j}")
  let word (ws : Array Name) : Expr :=
    mkApp2 (mkConst `CFSG.KC.BM.mulWn) nE (mkList listNatE (ws.map fun w => mkConst (rel P w)))
  withSync do
    let mut tot := 0.0
    for j in [0:69] do
      let lhs := mkApp (word (bs.map (·.getId))) (strip a.getId j)
      let rhs := mkApp (word (ds.map (·.getId))) (strip c.getId j)
      tot := tot + (← addTrueThm (P ++ tag.getId.appendAfter s!"_{j}") (mkApp2 (mkConst ``Nat.beq) lhs rhs))
    logInfo m!"BMTIME {tag.getId} {tot} ms"

elab "#bm_mul " pre:ident tag:ident a:ident "[" bs:ident* "]" c:ident "[" ds:ident* "]" : command => do
  let P := pre.getId
  withSync do
    let mut tot := 0.0
    for j in [0:(N + 63) / 64] do
      let lhs := mkApp (wordE P (bs.map (·.getId))) (stripE P a.getId j)
      let rhs := mkApp (wordE P (ds.map (·.getId))) (stripE P c.getId j)
      tot := tot + (← addTrueThm (P ++ tag.getId.appendAfter s!"_{j}") (mkApp2 (mkConst ``Nat.beq) lhs rhs))
    logInfo m!"BMTIME {tag.getId} {tot} ms"

declare_syntax_cat bmterm
syntax num : bmterm
syntax ident : bmterm
syntax "(" ident bmterm* ")" : bmterm
syntax "[" bmterm* "]" : bmterm

meta partial def CFSG.KC.BM.Load.bmTerm (P : Name) : TSyntax `bmterm → Except String Expr
  | `(bmterm| $n:num) => .ok (mkRawNatLit n.getNat)
  | `(bmterm| $i:ident) =>
    if i.getId == `true then .ok (mkConst ``Bool.true)
    else if i.getId == `false then .ok (mkConst ``Bool.false)
    else .ok (mkConst (rel P i.getId))
  | `(bmterm| ($f:ident $args*)) => do
    if f.getId == `L2 then return mkList listNatE (← args.mapM (bmTerm P))
    if f.getId == `L3 then return mkList (mkApp (mkConst ``List [0]) listNatE) (← args.mapM (bmTerm P))
    .ok (mkAppN (mkConst (rel P f.getId)) (← args.mapM (bmTerm P)))
  | `(bmterm| [$args*]) => do .ok (mkList natE (← args.mapM (bmTerm P)))
  | _ => .error "bad bmterm"

elab "#bm_bool " pre:ident tag:ident t:bmterm : command => do
  let P := pre.getId
  match bmTerm P t with
  | .error e => throwError e
  | .ok e => withSync do
    let ms ← addTrueThm (P ++ tag.getId) e
    logInfo m!"BMTIME {tag.getId} {ms} ms"

elab "#bm_defN " pre:ident tag:ident t:bmterm : command => do
  match bmTerm pre.getId t with
  | .error e => throwError e
  | .ok e => withSync <| addDef (pre.getId ++ tag.getId) natE e

elab "#bm_defL " pre:ident tag:ident t:bmterm : command => do
  match bmTerm pre.getId t with
  | .error e => throwError e
  | .ok e => withSync <| addDef (pre.getId ++ tag.getId) listNatE e

elab "#bm_hash_repo " paths:str* : command => do
  for p in paths do
    let b ← IO.FS.readBinFile p.getString
    logInfo m!"PIN {p.getString} {b.size} {b.hash.toNat}"

elab "#bm_hash " paths:str* : command => do
  let root ← dataRoot
  for p in paths do
    let b ← IO.FS.readBinFile (root / p.getString)
    logInfo m!"PIN {p.getString} {b.size} {b.hash.toNat}"
