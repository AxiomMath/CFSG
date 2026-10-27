module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8Wr

open CFSG.QuasithinUnique.A6Facts

@[expose] def c0 (i : Nat) : List Nat := Core.p0Lit.getD i []

@[expose] def t0 (a b : Nat) : Nat := Core.p0Lit.idxOf (Core.cmul (c0 a) (c0 b))

@[expose] def i0 : Nat := Core.p0Lit.idxOf Core.cid

@[expose] def mtab (_ : Unit := ()) : Array Nat :=
  Array.ofFn (n := 1024) fun k => t0 (k.val / 32) (k.val % 32)

@[expose] def mulI (M : Array Nat) (x y : Nat × Nat × Bool) : Nat × Nat × Bool :=
  if x.2.2 then (M.getD (x.1 * 32 + y.2.1) 0, M.getD (x.2.1 * 32 + y.1) 0, !y.2.2)
  else (M.getD (x.1 * 32 + y.1) 0, M.getD (x.2.1 * 32 + y.2.1) 0, y.2.2)

@[expose] def oneI : Nat × Nat × Bool := (i0, i0, false)

@[expose] def elemsI : List (Nat × Nat × Bool) :=
  (List.range 32).flatMap fun a => (List.range 32).flatMap fun b => [(a, b, false), (a, b, true)]

@[expose] def preOK (M : Array Nat) (z t a : Nat × Nat × Bool) : Bool :=
  (mulI M z z == oneI) && (mulI M a a == oneI) && (mulI M t t == oneI) &&
    (a != oneI) && (t != oneI) && (a != t) && (mulI M a t == mulI M t a) &&
    (mulI M z t == mulI M t z) && (mulI M z a == mulI M (mulI M a t) z)

@[expose] def cOK (M : Array Nat) (t a c : Nat × Nat × Bool) : Bool :=
  (mulI M c c == oneI || mulI M c c == t) && (mulI M c a == mulI M a c) &&
    (mulI M c t == mulI M t c)

@[expose] def relOK (M : Array Nat) (z t a at' g₁ g₂ : Nat × Nat × Bool) : Bool :=
  mulI M g₁ g₂ == mulI M at' (mulI M g₂ g₁) &&
    (let h₁ := mulI M (mulI M z g₁) z
     let h₂ := mulI M (mulI M z g₂) z
     mulI M h₁ h₂ == mulI M a (mulI M h₂ h₁) &&
     mulI M g₁ h₂ == mulI M t (mulI M h₂ g₁) &&
     mulI M g₂ h₁ == mulI M t (mulI M h₁ g₂) &&
     mulI M g₁ h₁ == mulI M h₁ g₁ && mulI M g₂ h₂ == mulI M h₂ g₂ &&
     mulI M h₁ a == mulI M a h₁ && mulI M h₁ t == mulI M t h₁ &&
     mulI M h₂ a == mulI M a h₂ && mulI M h₂ t == mulI M t h₂)

@[expose] def sigmaCheck (_ : Unit := ()) : Bool :=
  let M := mtab ()
  let L := elemsI
  let inv := L.filter fun x => x != oneI && mulI M x x == oneI
  inv.all fun z => inv.all fun t => inv.all fun a =>
    if preOK M z t a then
      (let C := L.filter fun c => cOK M t a c
       let at' := mulI M a t
       C.all fun g₁ => C.all fun g₂ => !(relOK M z t a at' g₁ g₂))
    else true

@[expose] def p0Ok (_ : Unit := ()) : Bool :=
  (List.range 32).all (fun a => (List.range 32).all fun b =>
    Core.p0Lit.contains (Core.cmul (c0 a) (c0 b))) &&
    Core.p0Lit.contains Core.cid && (c0 i0 == Core.cid)

@[expose] def wrCheck (_ : Unit := ()) : Bool := p0Ok () && sigmaCheck ()

end CFSG.EvenSporadicStandard.Fin76b.TS8Wr
