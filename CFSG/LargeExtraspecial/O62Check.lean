module

public import CFSG.LargeExtraspecial.O62Model
public import CFSG.LargeExtraspecial.O62Data

public section

set_option compiler.extract_closed false

namespace CFSG.LargeExtraspecial.O62

namespace Check

open Code

@[expose] def isInv (c : ℕ) : Bool := mul c c == one && c != one

@[expose] def comm (x y : ℕ) : Bool := mul x y == mul y x

@[expose] def spanC : List ℕ → List ℕ
  | [] => [one]
  | x :: xs => spanC xs ++ (spanC xs).map fun c => mul c x

@[expose] def sylowWords : Bool → List (List ℕ)
  | false => sylowWordsPlus
  | true => sylowWordsMinus

@[expose] def certs : Bool → List (ℕ × List ℕ)
  | false => certsPlus
  | true => certsMinus

@[expose] def checkSylow (minus : Bool) : Bool :=
  let Tw := sylowWords minus
  let cs := Tw.map wordC
  Tw.all (fun w => w.all (qB minus)) && Tw.contains [] &&
    cs.all (fun x => cs.all fun y => cs.contains (mul x y)) &&
    Tw.all (fun w => cs.contains (wordC w.reverse)) && decide cs.Nodup &&
    Tw.length == 128 && (Tw.filter fun w => w.length % 2 == 0).length == 64

@[expose] def checkRank (minus : Bool) : Bool :=
  let cs := ((sylowWords minus).map wordC).filter isInv
  cs.all fun x₁ =>
    let s₁ := spanC [x₁]
    let c₁ := cs.filter fun y => comm x₁ y && !s₁.contains y
    c₁.all fun x₂ =>
      let s₂ := s₁ ++ s₁.map fun c => mul c x₂
      let c₂ := c₁.filter fun y => comm x₂ y && !s₂.contains y
      c₂.all fun x₃ =>
        let s₃ := s₂ ++ s₂.map fun c => mul c x₃
        let c₃ := c₂.filter fun y => comm x₃ y && !s₃.contains y
        c₃.all fun x₄ =>
          let s₄ := s₃ ++ s₃.map fun c => mul c x₄
          (c₃.filter fun y => comm x₄ y && !s₄.contains y).isEmpty

@[expose] def keyOf (E : List ℕ) : ℕ := (E.map fun c => c ^ 3).sum

@[expose] def certOK (E k : List ℕ) : Bool :=
  let K := wordC k
  let Ki := wordC k.reverse
  let conjs := E.map fun e => mul (mul K e) Ki
  conjs.all (fun y => E.all fun f => E.contains (mul (mul y f) y)) &&
    conjs.any fun y => !E.contains y

@[expose] def wcTriple (minus : Bool) (a b c : List ℕ) (x y z : ℕ) : Bool :=
  if comm x y && comm x z && comm y z && !(spanC [x]).contains y &&
      !(spanC [y, x]).contains z then
    let E := spanC [z, y, x]
    let ev := a.length % 2 == 0 && b.length % 2 == 0 && c.length % 2 == 0
    decide E.Nodup && ((!minus && ev) || (certs minus).any fun p =>
      p.1 == keyOf E && p.2.all (qB minus) && (!ev || p.2.length % 2 == 0) && certOK E p.2)
  else true

@[expose] def checkWC (minus : Bool) : Bool :=
  let ps := ((sylowWords minus).filter fun w => isInv (wordC w)).map fun w => (w, wordC w)
  ps.all fun p => ps.all fun q =>
    if comm p.2 q.2 && !(spanC [p.2]).contains q.2 then
      ps.all fun r => wcTriple minus p.1 q.1 r.1 p.2 q.2 r.2
    else true

end Check

end CFSG.LargeExtraspecial.O62
