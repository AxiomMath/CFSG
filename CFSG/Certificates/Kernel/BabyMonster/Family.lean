module

public import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public meta import Lean

open Lean Elab Command

namespace CFSG.KC.BM.Family

meta partial def reinfo (i : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node i k (args.map (reinfo i))
  | .atom _ v => .atom i v
  | .ident _ r v p => .ident i r v p
  | .missing => .missing

meta def isNum (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

meta def identOf (s : String) : Except String Ident := do
  let n := s.toName
  let ok := !n.isAnonymous && n.components.all fun c => match c with
    | .str _ c => !c.isEmpty && (c.front.isAlpha || c.front == '_') &&
        c.all fun ch => ch.isAlphanum || ch == '_' || ch == '\''
    | _ => false
  unless ok do throw s!"`{s}` is not an identifier"
  return mkIdent n

meta def numOf (s : String) : Except String NumLit := do
  unless isNum s do throw s!"`{s}` is not a numeral"
  return Syntax.mkNumLit s

meta def sides (ts : List String) : Except String (Ident × Array Ident × Ident × Array Ident) := do
  match ts.splitOn "=" with
  | [a :: bs, c :: ds] =>
    return (← identOf a, ← (bs.mapM identOf).map List.toArray, ← identOf c,
      ← (ds.mapM identOf).map List.toArray)
  | _ => throw "expected `A B₁ … = C D₁ …`"

meta partial def records (env : Environment) (pre : Ident) (ts : List String) (acc : Array Syntax) :
    CommandElabM (Array Syntax) := do
  let lift {α} (x : Except String α) : CommandElabM α := match x with
    | .ok a => pure a
    | .error e => throwError e
  let term (ws : List String) : CommandElabM (TSyntax `bmterm) :=
    lift <| (Parser.runParserCategory env `bmterm (" ".intercalate ws) "<record>").map (⟨·⟩)
  match ts with
  | "eval" :: x :: f :: args =>
    let args ← args.toArray.mapM fun a => do
      if isNum a then `(kcEvalArg| $(Syntax.mkNumLit a):num)
      else
        let i ← lift (identOf a)
        `(kcEvalArg| $i:ident)
    let x ← lift (identOf x)
    let f ← lift (identOf f)
    return acc.push (← `(command| #kc_eval $pre $x $f $args*))
  | "mul" :: tag :: rest =>
    let tag ← lift (identOf tag)
    let (a, bs, c, ds) ← lift (sides rest)
    return acc.push (← `(command| #bm_mul $pre $tag $a [$bs*] $c [$ds*]))
  | "muln" :: n :: tag :: rest =>
    let n ← lift (numOf n)
    let tag ← lift (identOf tag)
    let (a, bs, c, ds) ← lift (sides rest)
    return acc.push (← `(command| #bm_muln $pre $n $tag $a [$bs*] $c [$ds*]))
  | "mul4" :: tag :: rest =>
    let tag ← lift (identOf tag)
    let (a, bs, c, ds) ← lift (sides rest)
    return acc.push (← `(command| #bm_mul4 $pre $tag $a [$bs*] $c [$ds*]))
  | "bool" :: tag :: t =>
    let tag ← lift (identOf tag)
    let t ← term t
    return acc.push (← `(command| #bm_bool $pre $tag $t))
  | "neg" :: tag :: t =>
    let tag ← lift (identOf tag)
    let t ← term t
    let t ← `(bmterm| ($(mkIdent `CFSG.KC.BM.notB):ident $t))
    return acc.push (← `(command| #bm_bool $pre $tag $t))
  | ["wf", x] =>
    let tag ← lift (identOf s!"wf_{x}")
    let x ← lift (identOf x)
    let t ← `(bmterm| ($(mkIdent `CFSG.KC.BM.wfMat):ident $x:ident))
    return acc.push (← `(command| #bm_bool $pre $tag $t))
  | "for" :: v :: lo :: hi :: r =>
    unless isNum lo && isNum hi do throwError "expected `for v lo hi record`"
    let mut acc := acc
    for k in [lo.toNat!:hi.toNat!] do
      acc ← records env pre (r.map (·.replace s!"\{{v}}" (toString k))) acc
    return acc
  | _ => throwError "unknown record"

meta def pkgRoot : CommandElabM System.FilePath := do
  let m ← getMainModule
  if m.isAnonymous || m == `_stdin then return "."
  let mut p := System.FilePath.mk (← getFileName)
  for _ in m.components do
    p := p.parent.getD "."
  return if p.toString.isEmpty then "." else p

meta def readFile (rel : String) (size hash : Nat) : CommandElabM ByteArray := do
  let b ← IO.FS.readBinFile ((← pkgRoot) / rel)
  unless b.size == size && b.hash.toNat == hash do
    throwError "#bm_family {rel}: size {b.size} hash {b.hash.toNat}, pinned {size} {hash}"
  return b

end CFSG.KC.BM.Family

open CFSG.KC.BM.Family in
elab "#bm_family " pre:ident path:str size:num hash:num : command => do
  let rel := path.getString
  let t0 ← IO.monoNanosNow
  let b ← readFile rel size.getNat hash.getNat
  let some text := String.fromUTF8? b | throwError "#bm_family {rel}: not UTF-8"
  let env ← getEnv
  let info := SourceInfo.fromRef (← getRef) (canonical := false)
  let mut cmds : Array Syntax := #[]
  let mut ln : Nat := 0
  for line in text.splitOn "\n" do
    ln := ln + 1
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "--" then continue
    let ts := (line.splitOn " ").filter (!·.isEmpty)
    let cs ← try records env pre ts #[]
      catch ex => throwError m!"#bm_family {rel}:{ln}: {ex.toMessageData}"
    cmds := cmds ++ cs.map (reinfo info)
  let t1 ← IO.monoNanosNow
  for c in cmds do
    elabCommand c
  let t2 ← IO.monoNanosNow
  let ms (a b : Nat) : Float := (b - a).toFloat / 1e6
  logInfo m!"FAMTIME {rel} commands {cmds.size} read+parse {ms t0 t1} elab {ms t1 t2} ms"
