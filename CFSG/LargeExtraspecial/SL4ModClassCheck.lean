module

public import CFSG.LargeExtraspecial.SL4ModNativeSpin

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def reduceMask (b bm : Array Nat) (w mk : Nat) : Nat × Nat :=
  (List.range b.size).foldl (fun (vm : Nat × Nat) t =>
    if vm.1 ^^^ b[t]! < vm.1 then (vm.1 ^^^ b[t]!, vm.2 ^^^ bm[t]!) else vm) (w, mk)

@[expose] def echelon (L : Array Nat) : Array Nat × Array Nat :=
  (List.range L.size).foldl (fun (st : Array Nat × Array Nat) t =>
    let r := reduceMask st.1 st.2 L[t]! (1 <<< t)
    if r.1 == 0 then st else (st.1.push r.1, st.2.push r.2)) (#[], #[])

@[expose] def solveMask (e : Array Nat × Array Nat) (w : Nat) : Nat :=
  (reduceMask e.1 e.2 w 0).2

@[expose] def spinEch (taus : Array (Array Nat)) (m cap : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat :=
  Id.run do
    let mut L : Array Nat := #[m]
    let mut src : Array (Nat × Nat) := #[(0, 0)]
    let mut basis : Array Nat := if m == 0 then #[] else #[m]
    let mut bmask : Array Nat := if m == 0 then #[] else #[1]
    let mut masks : Array Nat := #[1]
    let mut piv : Array Nat := #[Nat.log2 m]
    let mut q := 0
    for _ in [0:cap + 1] do
      if q < L.size && L.size < cap then
        for s in [0:6] do
          if L.size < cap then
            let w := actV taus[s]! L[q]!
            let r := reduceMask basis bmask w (1 <<< L.size)
            if r.1 != 0 then
              L := L.push w
              src := src.push (s, q)
              basis := basis.push r.1
              bmask := bmask.push r.2
              masks := masks.push r.2
              piv := piv.push (Nat.log2 r.1)
        q := q + 1
    return (L, src, masks, piv)

@[expose] def classMatrix (taus : Array (Array Nat)) (L : Array Nat) : Array (Array Nat) :=
  let e := echelon L
  Array.ofFn (n := 6) fun s =>
    Array.ofFn (n := L.size) fun k => solveMask e (actV taus[s.val]! L[k.val]!)

structure ClassCert where
  L : Array Nat
  src : Array (Nat × Nat)
  kind : Nat
  masks : Array Nat
  piv : Array Nat
  sel : Nat
  B : Array Nat
  coef : Array Nat
  mB : Nat
  ref : Nat
deriving Inhabited

@[expose] def echelonOK (n : Nat) (L masks piv : Array Nat) : Bool :=
  decide (n ≤ masks.size) && decide (n ≤ piv.size) &&
    (List.range n).all fun k =>
      decide (piv[k]! < 105) && (xorSel masks[k]! L).testBit piv[k]! &&
        (List.range n).all fun j => decide (j ≤ k) || !((xorSel masks[j]! L).testBit piv[k]!)

@[expose] def closedC (taus : Array (Array Nat)) (B coef : Array Nat) : Bool :=
  (List.range B.size).all fun t => (List.range 6).all fun s =>
    xorSel coef[6 * t + s]! B == actV taus[s]! B[t]!

@[expose] def refOK (taus : Array (Array Nat)) (L : Array Nat) (rows : Array (Array Nat)) : Bool :=
  decide (rows.size = 6) && (List.range 6).all fun s =>
    decide (rows[s]!.size = L.size) && (List.range L.size).all fun k =>
      xorSel rows[s]![k]! L == actV taus[s]! L[k]!

@[expose] def validClass (d : Nat) (refs : Array (Array (Array Nat))) (taus : Array (Array Nat))
    (m : Nat) (c : ClassCert) : Bool :=
  derivOK taus m c.L c.src &&
    (if c.kind == 0 then decide (d + 1 ≤ c.L.size) && echelonOK (d + 1) c.L c.masks c.piv
    else if c.kind == 1 then
      nz (xorSel c.sel c.L) && decide (c.B.size < d) &&
        (xorSel c.mB c.B == xorSel c.sel c.L) && closedC taus c.B c.coef
    else if c.kind == 2 then
      decide (c.L.size = d) && decide (c.ref < refs.size) && refOK taus c.L refs[c.ref]!
    else false)

@[expose] def genClass (d : Nat) (refs : Array (Array (Array Nat)))
    (hints : List (Nat × Nat × Nat × Nat)) (taus : Array (Array Nat)) (j i c m : Nat) :
    ClassCert :=
  let sp := spinEch taus m (d + 1)
  let L := sp.1
  if d + 1 ≤ L.size then
    { L, src := sp.2.1, kind := 0, masks := sp.2.2.1, piv := sp.2.2.2, sel := 0, B := #[],
      coef := #[], mB := 0, ref := 0 }
  else
    let small (sel : Nat) : ClassCert :=
      let B := (spinBFS taus (xorSel sel L) (d + 1)).1
      let e := echelon B
      { L, src := sp.2.1, kind := 1, masks := #[], piv := #[], sel, B,
        coef := Array.ofFn (n := 6 * B.size) fun k =>
          solveMask e (actV taus[k.val % 6]! B[k.val / 6]!),
        mB := 1, ref := 0 }
    if L.size < d then small 1
    else match hints.find? (fun h => h.1 == j && h.2.1 == i && h.2.2.1 == c) with
      | some h => small h.2.2.2
      | none =>
        { L, src := sp.2.1, kind := 2, masks := #[], piv := #[], sel := 0, B := #[],
          coef := #[], mB := 0,
          ref := (refs.findIdx? (· == classMatrix taus L)).getD refs.size }

@[expose] def checkClass (d : Nat) (refs : Array (Array (Array Nat)))
    (hints : List (Nat × Nat × Nat × Nat)) : Bool :=
  (List.range 3).all fun j =>
    let dj := cosetData j
    checkTau j dj && (List.range 3).all fun i =>
      let od := orbData dj i
      checkOrb dj i od && (List.range 128).all fun c => c == 0 ||
        validClass d refs dj.tau (expand od c) (genClass d refs hints dj.tau j i c (expand od c))

end CFSG.LargeExtraspecial.SL4Mod.Native
