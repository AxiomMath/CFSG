module

public import CFSG.Certificates.Kernel.Bounds.Core3
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Bounds.Load

open Lean Elab Command

public section

namespace CFSG.Certificates.KB

@[expose] noncomputable def wordOkB' (R S : Nat → Nat) (inv nR nS wd : Nat) (vm : Nat × Nat) :
    Bool :=
  Prod.rec (motive := fun _ => Bool) (fun v m =>
    Bool.rec
      (orB (Nat.beq (freeRed inv v m) (nat_lit 0))
        (andB (Nat.ble (Nat.succ (wBase wd)) nR)
          (andB (Nat.beq (wN (R (wBase wd))) m) (isRot (wLetters (R (wBase wd))) m v))))
      (andB (Nat.ble (Nat.succ (wBase wd)) nS)
        (andB (Nat.beq (wN (S (wBase wd))) m) (Nat.beq (wLetters (S (wBase wd))) v)))
      (Nat.beq (wKind wd) (nat_lit 1))) vm

@[expose] noncomputable def wordOkB (R S : Nat → Nat) (inv eps nR nS wd : Nat) : Bool :=
  wordOkB' R S inv nR nS wd (strip eps (wLetters wd) (wN wd))

@[expose] noncomputable def wordsOkB (Wd R S : Nat → Nat) (inv eps nR nS n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => Bool.rec false
      (Bool.rec false acc (lettersLe eps (Wd i))) (wordOkB R S inv eps nR nS (Wd i))) n

end CFSG.Certificates.KB

namespace CFSG.Certificates.KB.Checks

meta structure Header where
  fields : Std.HashMap String (Array Nat)
  inv : Nat

meta def parseHeader (b : ByteArray) : Header := Id.run do
  let mut fields : Std.HashMap String (Array Nat) := {}
  let mut inv := 0
  let mut i := 0
  while i < b.size do
    let mut j := i
    while j < b.size && b[j]! != 32 && b[j]! != 10 do j := j + 1
    let key := String.fromUTF8! (b.extract i j)
    let mut vals : Array Nat := #[]
    let mut acc := 0
    let mut inNum := false
    while j < b.size && b[j]! != 10 do
      let c := b[j]!
      if key == "invhex" then
        if c != 32 then
          inv := inv * 16 + (if c ≥ 97 then (c - 87).toNat else (c - 48).toNat)
      else if c ≥ 48 && c ≤ 57 then
        acc := acc * 10 + (c - 48).toNat
        inNum := true
      else if inNum then
        vals := vals.push acc
        acc := 0
        inNum := false
      j := j + 1
    if inNum then vals := vals.push acc
    fields := fields.insert key vals
    i := j + 1
  return { fields, inv }

meta def Header.get (h : Header) (k : String) : Nat := (h.fields.getD k #[0])[0]!

meta def natT (_ : Unit := ()) : Expr := mkConst ``Nat
meta def lit (n : Nat) : Expr := mkRawNatLit n
meta def kb (s : String) : Expr := mkConst (`CFSG.Certificates.KB ++ s.toName)

meta def shifted (T : Expr) (k0 : Nat) : Expr :=
  mkLambda `i .default natT (mkApp T (mkApp2 (mkConst ``Nat.add) (.bvar 0) (lit k0)))

meta def beqE (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.beq) a b

meta def perModule : Nat := 2000
meta def perPart : Nat := 20000

meta def thm (D : Name) (h : Header) (wf cx : Array Nat) (t : Nat) : Nat × String × Expr :=
  let c := fun (s : String) => mkConst (D ++ s.toName)
  let L := h.get "L"; let eps := h.get "EPS"; let nLab := h.get "nLab"; let nT := h.get "nT"
  let N := h.get "N"; let RW := h.get "RW"; let nW := h.get "nWords"
  let nR := h.get "R"; let nS := h.get "K"
  let nF := nT + h.get "nWalk"
  let RM := (1 <<< RW) - 1
  let nWC := (nW + 999) / 1000
  let nTC := (nT + 299) / 300
  let nWE := wf.size - 1
  if t < 2 * nWC then
    let k := t / 2
    let k0 := 1000 * k
    let cnt := min 1000 (nW - k0)
    if t % 2 == 0 then
      (0, s!"words{k}", mkAppN (kb "wordsOkB")
        #[shifted (c "Wd") k0, c "R", c "S", lit h.inv, lit eps, lit nR, lit nS, lit cnt])
    else
      (1, s!"pairs{k}", mkAppN (kb "words2Ok")
        #[shifted (c "Wd") k0, shifted (c "Wd2") k0, lit h.inv, lit cnt])
  else if t < 2 * nWC + nTC then
    let k := t - 2 * nWC
    (2, s!"tree{k}", mkAppN (kb "treeRange")
      #[c "F", c "D", lit L, lit nLab, lit (300 * k), lit (min 300 (nT - 300 * k))])
  else if t < 2 * nWC + nTC + nWE then
    let j := t - 2 * nWC - nTC
    let el := c s!"wl{j / perPart}.c{j % perPart}"
    (3, s!"walk{j}", beqE (mkAppN (kb "wWalkList")
      #[c "F", c "Wd2", lit RW, lit RM, lit nLab, lit nW, el, lit wf[j]!]) (lit wf[j + 1]!))
  else
    let j := t - 2 * nWC - nTC - nWE
    let el := c s!"cv{j / perPart}.c{j % perPart}"
    (4, s!"cov{j}", beqE (mkAppN (kb "wCovList")
      #[c "F", lit RW, lit RM, lit N, lit L, lit nF, el, lit cx[j]!]) (lit cx[j + 1]!))

meta def scan (s : Nat) (a : Array Nat) : Array Nat := Id.run do
  let mut out := Array.mkEmpty (a.size + 1)
  let mut acc := s
  out := out.push acc
  for x in a do
    acc := acc + x
    out := out.push acc
  return out

end CFSG.Certificates.KB.Checks

open CFSG.Certificates.KB.Checks in
elab "#kb_checks " p:ident "include_bytes" path:str size:num hash:num m:num : command => do
  let b ← CFSG.Certificates.KB.Load.readPinned path.getString size.getNat hash.getNat
  let h := parseHeader b
  let P := p.getId
  let D := `CFSG.KBData ++ P
  let wf := scan (h.get "nT") (h.fields.getD "walkElems" #[])
  let cx := scan 0 (h.fields.getD "covElems" #[])
  let nWC := (h.get "nWords" + 999) / 1000
  let total := 2 * nWC + (h.get "nT" + 299) / 300 + (wf.size - 1) + (cx.size - 1)
  unless wf.back! == h.get "nT" + h.get "nWalk" && cx.back! == h.get "N" do
    throwError "header {path.getString}: element sizes do not sum to nWalk and N"
  let lo := perModule * m.getNat
  let hi := min total (lo + perModule)
  if hi ≤ lo then throwError "module {m.getNat} is past the {total} checks of {P}"
  for t in [lo:hi] do
    let (_, nm, e) := thm D h wf cx t
    let name := `CFSG.KBCheck3 ++ P ++ nm.toName
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
    CFSG.Certificates.KB.Load.withSync <| CFSG.KC.addThmDecl <|
      { name, levelParams := [], type, value := reflBoolTrue }

end
