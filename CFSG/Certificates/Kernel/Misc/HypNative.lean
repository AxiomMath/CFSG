module

public import CFSG.Certificates.Kernel.Misc.XiSound
public import CFSG.Certificates.Kernel.Misc.LinesSound

public section

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi

@[expose] def lineCG (U : Array Nat) (x y : Nat) : Array Nat :=
  let cx := U[x]!
  let cy := U[y]!
  #[x, y, (uPosG U)[normC (cx ^^^ cy)]!, (uPosG U)[normC (cx ^^^ scaleC 2 cy)]!,
    (uPosG U)[normC (cx ^^^ scaleC 3 cy)]!]

@[expose] def clStepG (U : Array Nat) (F : Flags) : Flags :=
  let M := members F
  M.foldl (fun a u => let T := (tvTabsG U)[u]!; M.foldl (fun a v => a.set! (ap T v) true) a) F

@[expose] def clIterG (U : Array Nat) : Nat → Flags → Flags
  | 0, F => F
  | k + 1, F => clIterG U k (clStepG U F)

@[expose] def lamTabG (U : Array Nat) (sel : Array Nat) : Array Flags :=
  Array.ofFn (n := 1024) fun j => clIterG U 3 (lamStart (sel.map (lineCG U 0)) j.val)

@[expose] def lamOKG (sel : Array Nat) (P : Array Flags) (LT : Array (Array Nat))
    (lam : Array Flags) : Bool :=
  let p0 := P[0]!
  sel.size == 5 && allIn 0 5 (fun i => sel[i]! < 693 && sel[i]! != 0 && p0[sel[i]!]!) &&
    lam.size == 1024 &&
    allIn 0 1024 fun j =>
      let F := lam[j]!
      F[0]! && allIn 0 693 (fun z => !F[z]! || p0[z]!) &&
        allIn 0 693 fun y => !p0[y]! || y == 0 || LT[y]!.any fun z => z != 0 && F[z]!

@[expose] def gWordsG (U : Array Nat) : Array (List Nat) := Id.run do
  let T := tvTabsG U
  let mut w : Array (List Nat) := Array.replicate 693 []
  let mut seen : Array Bool := (Array.replicate 693 false).set! 0 true
  let mut queue : Array Nat := #[0]
  for h in [0:693] do
    if h < queue.size then
      let x := queue[h]!
      for k in [0:31] do
        let p := 23 * k
        let y := ap T[p]! x
        if !seen[y]! then
          seen := seen.set! y true
          w := w.set! y (p :: w[x]!)
          queue := queue.push y
    else break
  return w

@[expose] def tvWordTabG (U : Array Nat) (w : List Nat) : Table :=
  w.foldr (fun p T => compT 693 (tvTabsG U)[p]! T) (idT 693)

@[expose] def mkCtxG (U : Array Nat) (P : Array Flags) (W : Array (List Nat)) (lam : Array Flags) :
    HCtx :=
  { P := P, pl := perpLists P, lam := lam,
    lamIdx := Array.ofFn (n := 693) fun p => filterRange (fun j => (lam[j]!)[p.val]!) 1024 [],
    gI := Array.ofFn (n := 693) fun x => invT 693 (tvWordTabG U W[x.val]!) }

@[expose] def wordsOKG (U : Array Nat) (W : Array (List Nat)) (gI : Array Table) : Bool :=
  W.size == 693 && gI.size == 693 &&
    allIn 0 693 fun x =>
      let w := W[x]!
      let T := tvWordTabG U w
      w.all (· < 693) && ap T 0 == x && invOK 693 T gI[x]!

@[expose] def rootOKG (U : Array Nat) (P : Array Flags) (LT : Array (Array Nat)) (R : Flags) :
    Bool :=
  R.size == 693 &&
    allIn 0 693 (fun x =>
      let px := P[x]!
      allIn 0 693 fun y => !(decide (x < y) && px[y]!) ||
        (let c := (LT[x * 693 + y]!.toList.filter (R[·]!)).length; c == 0 || c == 2)) &&
    (members R).all fun x => let T := (tvTabsG U)[x]!; allIn 0 693 fun q => R[q]! == R[ap T q]!

@[expose] def hypChecksG (U : Array Nat) (sel : Array Nat) (P : Array Flags) (LT : Array (Array Nat))
    (W : Array (List Nat)) (lam : Array Flags) (gs gi : Array Table)
    (o₀ o₁ o₂ : Array Flags × Array Nat × Array Nat) : Bool :=
  let C := mkCtxG U P W lam
  let H := o₀.1 ++ o₁.1 ++ o₂.1
  let ix := famIndex H
  lamOKG sel P LT lam && wordsOKG U W C.gI &&
    rootOKG U P LT (rootFlagsG U 1) && rootOKG U P LT (rootFlagsG U 2) &&
    rootOKG U P LT (rootFlagsG U 3) &&
    hypOrbitOK (rootFlagsG U 1) gs gi o₀ ix 0 && hypOrbitOK (rootFlagsG U 2) gs gi o₁ ix 1408 &&
    hypOrbitOK (rootFlagsG U 3) gs gi o₂ ix 2816 && famOK H ix && searchOK C H ix 40

@[expose] def hypG (U : Array Nat) (xw yw : List Int) (sel : Array Nat) : Bool :=
  let P := perpTabG U
  hypChecksG U sel P (lineTabG U P) (gWordsG U) (lamTabG U sel)
    #[powG U 3 xw, powG U 2 yw] #[powG U 3 xw, compT 693 (powG U 2 yw) (powG U 2 yw)]
    (hypEnumG U xw yw 1) (hypEnumG U xw yw 2) (hypEnumG U xw yw 3)

@[expose] def hypUnionG (U : Array Nat) (xw yw : List Int) : Array Flags :=
  (hypEnumG U xw yw 1).1 ++ (hypEnumG U xw yw 2).1 ++ (hypEnumG U xw yw 3).1

@[expose] def wordInvsG (U : Array Nat) (W : Array (List Nat)) : Array Table :=
  Array.ofFn (n := 693) fun x => invT 693 (tvWordTabG U W[x.val]!)

end CFSG.KC.Misc.Hyp

end
