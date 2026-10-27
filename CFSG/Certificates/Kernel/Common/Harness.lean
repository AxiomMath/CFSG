module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.DataRoot

open Lean Elab Command

namespace CFSG.KC.Load

meta def hexVal (c : UInt8) : Nat :=
  if c ≥ 48 && c ≤ 57 then (c - 48).toNat
  else if c ≥ 97 && c ≤ 102 then (c - 87).toNat
  else if c ≥ 65 && c ≤ 70 then (c - 55).toNat
  else 0

meta def isDelim (c : UInt8) : Bool :=
  c == 32 || c == 40 || c == 41 || c == 91 || c == 93 || c == 10 || c == 9 || c == 13

meta partial def tokEnd (b : ByteArray) (i stop : Nat) : Nat :=
  if i < stop && !isDelim b[i]! then tokEnd b (i + 1) stop else i

meta partial def hexNat (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 16 then
    Id.run do
      let mut acc := 0
      for i in [lo:hi] do
        acc := acc * 16 + hexVal b[i]!
      return acc
  else
    let mid := (lo + hi) / 2
    (hexNat b lo mid <<< (4 * (hi - mid))) + hexNat b mid hi

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

meta partial def skipWs (b : ByteArray) (i stop : Nat) : Nat :=
  if i < stop && (b[i]! == 32 || b[i]! == 9 || b[i]! == 13) then skipWs b (i + 1) stop else i

meta def resolve (pre : Name) (s : String) : Name :=
  let n := s.toName
  let r := n.getRoot
  if pre.isAnonymous || r == `Nat || r == `Bool || r == `List || r == `CFSG then n
  else if r == `KTh then pre ++ n.replacePrefix `KTh .anonymous
  else pre ++ n

meta def tokName (pre : Name) (b : ByteArray) (lo hi : Nat) : Name :=
  resolve pre (String.fromUTF8! (b.extract lo hi))

meta def natE (_ : Unit := ()) : Expr := mkConst ``Nat
meta def boolE (_ : Unit := ()) : Expr := mkConst ``Bool
meta def listNatE (_ : Unit := ()) : Expr := mkApp (mkConst ``List [0]) natE

meta def mkNatList (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) natE e acc)
    (mkApp (mkConst ``List.nil [0]) natE)

meta def mkBIf (c t e : Expr) : Expr :=
  mkApp4 (mkConst ``Bool.rec [1]) (mkLambda `_ .default boolE boolE) e t c

meta partial def parseTerm (pre : Name) (b : ByteArray) (i stop : Nat) :
    Except String (Expr × Nat) := do
  let i := skipWs b i stop
  if i ≥ stop then throw "unexpected end of term"
  let c := b[i]!
  if c == 40 || c == 91 then
    let close : UInt8 := if c == 40 then 41 else 93
    let mut args : Array Expr := #[]
    let mut j := i + 1
    let mut head : Option String := none
    if c == 40 then
      let s := skipWs b j stop
      let e := tokEnd b s stop
      head := some (String.fromUTF8! (b.extract s e))
      j := e
    repeat
      j := skipWs b j stop
      if j ≥ stop then throw "unclosed bracket"
      if b[j]! == close then break
      let (a, j') ← parseTerm pre b j stop
      args := args.push a
      j := j'
    match head with
    | none => return (mkNatList args, j + 1)
    | some "bIf" =>
      if args.size != 3 then throw "bIf takes three arguments"
      return (mkBIf args[0]! args[1]! args[2]!, j + 1)
    | some "fld" =>
      if args.size != 3 then throw "fld takes three arguments"
      return (mkApp2 (mkConst ``Nat.land) (mkApp2 (mkConst ``Nat.shiftRight) args[0]! args[1]!)
        args[2]!, j + 1)
    | some h => return (mkAppN (mkConst (resolve pre h)) args, j + 1)
  else if c == 35 then
    let e := tokEnd b (i + 1) stop
    return (mkRawNatLit (hexNat b (i + 1) e), e)
  else
    let e := tokEnd b i stop
    let s := String.fromUTF8! (b.extract i e)
    if s == "true" then return (mkConst ``Bool.true, e)
    if s == "false" then return (mkConst ``Bool.false, e)
    return (mkConst (resolve pre s), e)

meta def addDef (name : Name) (type value : Expr) (expose : Bool) : CoreM Unit :=
  addDecl (forceExpose := expose) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

meta def addTrueThm (name : Name) (b : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <|
    { name, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) boolE b (mkConst ``Bool.true),
      value := reflBoolTrue }

meta def thmOfCheck (n : Name) : Name :=
  match n with
  | .str p s => if s.startsWith "c" then .str p ("t" ++ s.drop 1) else .str p (s ++ "_ok")
  | _ => n

meta def addLine (pre : Name) (checks : Bool) (b : ByteArray) (lo hi : Nat) : CoreM Unit := do
  let lo := skipWs b lo hi
  if lo + 2 > hi then return
  let kind := b[lo]!
  let ns := skipWs b (lo + 1) hi
  let ne := tokEnd b ns hi
  let name := tokName pre b ns ne
  let rest := skipWs b ne hi
  if kind == 78 then
    let e := tokEnd b rest hi
    addDef name natE (mkRawNatLit (hexNat b rest e)) true
  else
    match parseTerm pre b rest hi with
    | .error msg => throwError "line {name}: {msg}"
    | .ok (t, _) =>
      if kind == 66 then
        addDef name boolE t (!checks)
        if checks then addTrueThm (thmOfCheck name) (mkConst name)
      else if kind == 77 then addDef name natE t true
      else if kind == 76 then addDef name listNatE t true
      else if kind == 84 then addTrueThm name t
      else throwError "unknown declaration kind in line {name}"

meta def dataRoot {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m] : m System.FilePath :=
  CFSG.KC.dataRoot

meta def readPinned {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m]
    (rel : String) (size hash : Nat) : m ByteArray := do
  let path := (← dataRoot) / rel
  monadLift (m := IO) do
  let b ← IO.FS.readBinFile path
  let h := b.hash.toNat
  unless b.size == size && h == hash do
    let msg := s!"data file {path}: size {b.size} hash {h}, pinned size {size} hash {hash}"
    throw (IO.userError msg)
  return b

meta def withSync (x : CoreM Unit) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) x

meta def loadLines (pre : Name) (checks : Bool) (b : ByteArray) : CoreM Unit := do
  let mut lo := 0
  for i in [0:b.size] do
    if b[i]! == 10 then
      addLine pre checks b lo i
      lo := i + 1
  if lo < b.size then addLine pre checks b lo b.size

meta partial def bitDispatch (leafs : Array Expr) (p k : Nat) (off : Nat) (motive : Expr) : Expr :=
  if k == 0 then leafs[off]!
  else
    let bit := mkApp2 (mkConst ``Nat.beq)
      (mkApp2 (mkConst ``Nat.land) (.bvar 0) (mkRawNatLit (1 <<< (p - 1)))) (mkRawNatLit 0)
    let lo := bitDispatch leafs (p - 1) (k - 1) off motive
    let hi := bitDispatch leafs (p - 1) (k - 1) (off + (1 <<< (k - 1))) motive
    mkApp4 (mkConst ``Bool.rec [1]) motive hi lo bit

meta def fnT (_ : Unit := ()) : Expr := mkForall `b .default natE natE

meta partial def addKTreeNodes (leafName : Nat → Name) (name : Name) (lo h fan : Nat) :
    CoreM Unit := do
  let k := min fan h
  let children ← if k == h then
      pure <| (Array.range (1 <<< k)).map fun c => mkConst (leafName (lo + c))
    else
      (Array.range (1 <<< k)).mapM fun c => do
        let cn := name ++ Name.mkSimple s!"c{c}"
        addKTreeNodes leafName cn (lo + (c <<< (h - k))) (h - k) fan
        pure (mkApp (mkConst cn) (.bvar 0))
  addDef name fnT
    (mkLambda `b .default natE (bitDispatch children h k 0 (mkLambda `x .default boolE natE))) true

end CFSG.KC.Load

meta partial def CFSG.KC.Load.addSel (F : Name) (leaf : Nat → Expr) (lo hi b : Nat) : CoreM Unit := do
  if hi - lo ≤ 1 then return
  let mid := (lo + hi) / 2
  CFSG.KC.Load.addSel F leaf lo mid (b - 1)
  CFSG.KC.Load.addSel F leaf mid hi (b - 1)
  let child := fun l h =>
    if h - l == 1 then leaf l else mkApp (mkConst (F.appendAfter s!"_{l}_{b - 1}")) (.bvar 0)
  let bit := mkApp2 (mkConst ``Nat.blt) (mkRawNatLit 0)
    (mkApp2 (mkConst ``Nat.land) (.bvar 0) (mkRawNatLit (1 <<< b)))
  let body := mkApp4 (mkConst ``Bool.rec [1])
    (mkLambda `x .default CFSG.KC.Load.boolE CFSG.KC.Load.natE) (child lo mid) (child mid hi) bit
  CFSG.KC.Load.addDef (F.appendAfter s!"_{lo}_{b}") CFSG.KC.Load.fnT
    (mkLambda `k .default CFSG.KC.Load.natE body) true

elab "#kc_select " pre:ident id:ident base:ident n:num : command => do
  let n := n.getNat
  let d := max 1 (Nat.log2 (2 * n - 1))
  let F := pre.getId ++ id.getId
  let B := pre.getId ++ base.getId
  let leaf := fun k => if k < n then mkConst (B.appendAfter s!"{k}") else mkRawNatLit 0
  CFSG.KC.Load.withSync do
    CFSG.KC.Load.addSel F leaf 0 (1 <<< d) (d - 1)
    CFSG.KC.Load.addDef F CFSG.KC.Load.fnT
      (mkLambda `k .default CFSG.KC.Load.natE (mkApp (mkConst (F.appendAfter s!"_0_{d - 1}")) (.bvar 0))) true

elab "#kc_hash " paths:str* : command => do
  let root ← CFSG.KC.Load.dataRoot
  for p in paths do
    let b ← IO.FS.readBinFile (root / p.getString)
    logInfo m!"PIN {p.getString} {b.size} {b.hash.toNat}"

elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g => g.assign Lean.reflBoolTrue

elab "#load_decls " path:str : command => do
  let b ← IO.FS.readBinFile path.getString
  CFSG.KC.Load.withSync <| CFSG.KC.Load.loadLines .anonymous false b

open CFSG.KC.Load in
elab "#kc_decls " pre:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  withSync <| loadLines pre.getId false b

open CFSG.KC.Load in
elab "#kc_checks " pre:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  withSync <| loadLines pre.getId true b

meta partial def CFSG.KC.Load.partsOf (s : Syntax) : Array (String × Nat × Nat) :=
  if s.getNumArgs == 5 && s[0].isToken "(" then
    #[(s[1].isStrLit?.getD "", s[2].isNatLit?.getD 0, s[3].isNatLit?.getD 0)]
  else s.getArgs.foldl (fun acc a => acc ++ CFSG.KC.Load.partsOf a) #[]

meta def CFSG.KC.Load.readPinnedSrc {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m]
    (src : Syntax) (size hash : Nat) : m ByteArray := do
  if let some p := src.isStrLit? then return ← CFSG.KC.Load.readPinned p size hash
  let parts := CFSG.KC.Load.partsOf src
  let mut b := ByteArray.empty
  for (p, s, h) in parts do
    b := b ++ (← CFSG.KC.Load.readPinned p s h)
  monadLift (m := IO) do
  unless b.size == size && b.hash.toNat == hash do
    let msg := s!"data parts {parts.map (·.1)}: size {b.size} hash {b.hash.toNat}, \
      pinned size {size} hash {hash}"
    throw (IO.userError msg)
  return b

open CFSG.KC.Load in
elab "#kc_ktree " pre:ident id:ident src:(str <|> ("(" str num num ")")+) lb:num fan:num size:num
    hash:num : command => do
  let b ← readPinnedSrc src.raw size.getNat hash.getNat
  let F := pre.getId ++ id.getId
  let leafBytes := lb.getNat
  let nLeaves := (b.size + leafBytes - 1) / leafBytes
  let h := Nat.log2 (2 * nLeaves - 1)
  let leafName := fun k => if k < nLeaves then F ++ Name.mkSimple s!"L{k}" else F ++ `Z
  withSync do
    addDef (F ++ `Z) natE (mkRawNatLit 0) true
    for k in [0:nLeaves] do
      let s := k * leafBytes
      addDef (leafName k) natE (mkRawNatLit (natLE b s (min b.size (s + leafBytes)))) true
    addKTreeNodes leafName F 0 h fan.getNat

open CFSG.KC.Load in
elab "#kc_natBin " pre:ident id:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  withSync <| addDef (pre.getId ++ id.getId) natE (mkRawNatLit (natLE b 0 b.size)) true

meta def CFSG.KC.Load.decimalLines (b : ByteArray) : List Nat :=
  ((String.fromUTF8! b).splitOn "\n").filter (· ≠ "") |>.map String.toNat!

open CFSG.KC.Load in
elab "#kc_natList " pre:ident id:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  withSync <| addDef (pre.getId ++ id.getId) listNatE
    (mkNatList ((decimalLines b).toArray.map mkRawNatLit)) true

open CFSG.KC.Load in
elab "#kc_natLines " pre:ident id:ident path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  withSync do
    for (v, k) in (decimalLines b).zipIdx do
      addDef (pre.getId ++ id.getId ++ Name.mkSimple s!"n{k}") natE (mkRawNatLit v) true

open CFSG.KC.Load in
elab "#kc_listDispatch " pre:ident id:ident w:ident n:num : command => do
  let n := n.getNat
  let h := Nat.log2 (2 * n - 1)
  let W := pre.getId ++ w.getId
  let leafs := (Array.range (1 <<< h)).map fun k =>
    if k < n then mkConst (W.appendAfter s!"{k}") else mkNatList #[]
  let ty := mkForall `b .default natE listNatE
  withSync <| addDef (pre.getId ++ id.getId) ty
    (mkLambda `b .default natE (bitDispatch leafs h h 0 (mkLambda `x .default boolE listNatE))) true
