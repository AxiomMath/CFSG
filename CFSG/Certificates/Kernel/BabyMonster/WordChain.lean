module

public import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public meta import Lean

open Lean Elab Command

namespace CFSG.KC.BM.WordChain

meta def evalProd (pre x a : Ident) (bs : Array Ident) : CommandElabM Unit := do
  let args : Array (TSyntax `kcEvalArg) ← (#[a] ++ bs).mapM fun i => `(kcEvalArg| $i:ident)
  let n4370 := Syntax.mkNumLit "4370"
  let n0 := Syntax.mkNumLit "0"
  let prod := mkIdent `CFSG.KC.BM.Twin.prod
  elabCommand (← `(command|
    #kc_eval $pre $x $prod:ident $n4370:num $n0:num $n0:num $args*))
  let wf := mkIdent (Name.mkSimple s!"wf_{x.getId}")
  let wfMat := mkIdent `CFSG.KC.BM.wfMat
  elabCommand (← `(command| #bm_bool $pre $wf ($wfMat:ident $x:ident)))

meta def mulCheck (pre tag a : Ident) (bs : Array Ident) (c : Ident) : CommandElabM Unit := do
  elabCommand (← `(command| #bm_mul4 $pre $tag $a [$bs*] $c []))

meta def prodStep (pre a : Ident) (bs : Array Ident) (c : Ident) : CommandElabM Unit := do
  evalProd pre c a bs
  mulCheck pre (mkIdent (Name.mkSimple s!"c{c.getId}")) a bs c

meta def ident (s : String) : Ident := mkIdent (Name.mkSimple s)

meta def digits (e : Nat) : List Nat :=
  (List.range (Nat.log2 e + 1)).filter fun i => (e >>> i) % 2 == 1

end CFSG.KC.BM.WordChain

open CFSG.KC.BM.WordChain

elab "#bm_prod " pre:ident c:ident a:ident b:ident : command => prodStep pre a #[b] c

elab "#bm_pow " pre:ident g:ident p:num m:num : command => do
  let p := p.getNat
  unless 2 < p do throwError "#bm_pow: p = {p}"
  let h ← match m.getNat with
    | 1 => pure g
    | 2 => do
      let h := ident s!"G{p}"
      prodStep pre g #[g] h
      pure h
    | k => throwError "#bm_pow: m = {k}"
  let ds := digits (p - 1)
  let sq (i : Nat) : Ident := if i == 0 then h else ident s!"{h.getId}_sq{i}"
  for i in [1:ds.getLast!.succ] do
    prodStep pre (sq (i - 1)) #[sq (i - 1)] (sq i)
  let acc ← match ds with
    | [d] => pure (sq d)
    | d₀ :: d₁ :: rest => do
      let last := ident s!"G{p}p"
      let mut acc := sq d₀
      let mut i := 0
      let mut todo := d₁ :: rest
      while !todo.isEmpty do
        let d := todo.head!
        todo := todo.tail
        let dst := if todo.isEmpty then last else ident s!"G{p}pp{i}"
        prodStep pre acc #[sq d] dst
        acc := dst
        i := i + 1
      pure acc
    | [] => throwError "#bm_pow: p = 1"
  mulCheck pre (ident s!"ord_{p}") acc #[h] (ident "I")
  let ne := ident s!"ne_{p}"
  let notB := mkIdent `CFSG.KC.BM.notB
  let isId := mkIdent `CFSG.KC.BM.isId
  elabCommand (← `(command| #bm_bool $pre $ne ($notB:ident ($isId:ident $h:ident))))
