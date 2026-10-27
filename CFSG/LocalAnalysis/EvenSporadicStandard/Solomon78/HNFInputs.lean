module

public import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Sporadic.HNSchreier.ArchCheckInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFWalk
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFMoves
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Sporadic.HNSchreier.ArchCheckInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFWalk
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFMoves
public meta import Std.Data.HashSet
public import Std.Data.HashSet

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier.Native

abbrev hnfN : Nat := 1140000

@[expose] def hnfBytes : ByteArray := hexDumpBytes arraysPayload

@[expose] def hnfArch (B : ByteArray) (s : Nat) : Array Nat :=
  Array.ofFn (n := hnfN) fun i => le32 B (12 + 8 * i.val + 4 * s)

@[expose] def hnfInvWord (w : List Int) : List Int := w.reverse.map (fun l => -l)

@[expose] def hnfTabsOK (tA tAi tB tBi g1 g1i g2 g2i : Array Nat) : Bool :=
  pisInv hnfN tA tAi && pisInv hnfN tB tBi && pisInv hnfN g1 g1i && pisInv hnfN g2 g2i

@[expose] def orbitPts (G : Array (Array Nat)) (seed : Nat) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate hnfN false
  seen := seen.set! seed true
  let mut q : Array Nat := #[seed]
  let mut i := 0
  while i < q.size do
    let x := q[i]!
    for g in G do
      let y := g[x]!
      if !seen[y]! then
        seen := seen.set! y true
        q := q.push y
    i := i + 1
  return q

@[expose] def hnfPos (pts : Array Nat) : Array Nat := Id.run do
  let mut pos : Array Nat := Array.replicate hnfN pts.size
  for j in [0:pts.size] do
    pos := pos.set! pts[j]! j
  return pos

@[expose] def hnfIdx (Ginv pts pos : Array Nat) : Array Nat :=
  pts.map fun p => pos[Ginv[p]!]!

@[expose] def hnfPtsOK (G Ginv : Array (Array Nat)) (pts pos : Array Nat)
    (idx : Array (Array Nat)) : Bool :=
  idx.size == 3 && G.size == 3 && Ginv.size == 3 &&
    allBelowN pts.size (fun j => decide (pts[j]! < hnfN) && pos[pts[j]!]! == j &&
      allBelowN 3 (fun g => decide (idx[g]![j]! < pts.size) &&
        pts[idx[g]![j]!]! == Ginv[g]![pts[j]!]! &&
        decide (pos[G[g]![pts[j]!]!]! < pts.size)))

@[expose] def hnfStep (G : Array (Array Nat)) (idx : Array (Array Nat)) (g : Nat)
    (S : Array Nat) : Array Nat :=
  idx[g]!.map fun i => G[g]![S[i]!]!

@[expose] def hnfKey (kp : List Nat) (S : Array Nat) : Nat :=
  kp.foldr (fun p acc => S[p]! + 2097152 * acc) 0

@[expose] def hnfDecodeMoves (s : String) : List (Nat × Nat) :=
  (hexDumpBytes s).toList.map fun b => (b.toNat / 4, b.toNat % 4)

@[expose] def hnfRepTab (S Sinv : Array (Array Nat)) (g : List Int) : Array Nat :=
  pword hnfN S Sinv (g ++ [1] ++ hnfInvWord g)

@[expose] def hnfOrbitCore (tA tAi tB tBi g1 g1i g2 g2i : Array Nat) (seed : Nat) (g : List Int)
    (kp : List Nat) (moves : List (Nat × Nat)) (N : Nat) : Bool :=
  let G := #[tA, g1, g2]
  let Ginv := #[tAi, g1i, g2i]
  let pts := orbitPts G seed
  let pos := hnfPos pts
  let idx := #[hnfIdx tAi pts pos, hnfIdx g1i pts pos, hnfIdx g2i pts pos]
  let rep := hnfRepTab #[tA, tB] #[tAi, tBi] g
  let S0 := pts.map fun p => rep[p]!
  hnfTabsOK tA tAi tB tBi g1 g1i g2 g2i && hnfPtsOK G Ginv pts pos idx &&
    (hnfWalk 3 (hnfStep G idx) (hnfKey kp) moves [S0]
      ((∅ : Std.HashSet Nat).insert (hnfKey kp S0)) 1 == some N)

@[noinline, expose] def hnfOrbitCheck (B : ByteArray) (seed : Nat) (g : List Int)
    (kp : List Nat) (moves : List (Nat × Nat)) (N : Nat) : Bool :=
  let tA := hnfArch B 0
  let tB := hnfArch B 1
  let tAi := pinvCand hnfN tA
  let tBi := pinvCand hnfN tB
  let g1 := pword hnfN #[tA, tB] #[tAi, tBi] hnfW1
  let g2 := pword hnfN #[tA, tB] #[tAi, tBi] hnfW2
  hnfOrbitCore tA tAi tB tBi g1 (pinvCand hnfN g1) g2 (pinvCand hnfN g2) seed g kp moves N

@[expose] def hnfCountFix (t : Array Nat) : Nat := (List.range hnfN).countP fun i => t[i]! == i

@[expose] def hnfCountFixOn (pts t : Array Nat) : Nat :=
  (List.range pts.size).countP fun j => t[pts[j]!]! == pts[j]!

@[expose] def hnfSetupCore (tA tAi tB tBi g1 g1i g2 g2i : Array Nat) : Bool :=
  let G := #[tA, g1, g2]
  let Ginv := #[tAi, g1i, g2i]
  let pts := orbitPts G hnfSeedF
  let pos := hnfPos pts
  let idx := #[hnfIdx tAi pts pos, hnfIdx g1i pts pos, hnfIdx g2i pts pos]
  hnfTabsOK tA tAi tB tBi g1 g1i g2 g2i && hnfPtsOK G Ginv pts pos idx &&
    peq hnfN (pcomp hnfN g1 tA) (pcomp hnfN tA g1) &&
    peq hnfN (pcomp hnfN g2 tA) (pcomp hnfN tA g2) &&
    (List.range 9).all fun i =>
      let rep := hnfRepTab #[tA, tB] #[tAi, tBi] hnfRepWords[i]!
      hnfCountFix (pcomp hnfN tA rep) == (hnfInvs[i]!).1 && hnfCountFixOn pts rep == (hnfInvs[i]!).2

@[noinline, expose] def hnfSetupCheck (B : ByteArray) : Bool :=
  let tA := hnfArch B 0
  let tB := hnfArch B 1
  let tAi := pinvCand hnfN tA
  let tBi := pinvCand hnfN tB
  let g1 := pword hnfN #[tA, tB] #[tAi, tBi] hnfW1
  let g2 := pword hnfN #[tA, tB] #[tAi, tBi] hnfW2
  hnfSetupCore tA tAi tB tBi g1 (pinvCand hnfN g1) g2 (pinvCand hnfN g2)

@[expose] def hnfPtStep (s : Array (Array Nat)) (k : Nat) (S : Array Nat) : Array Nat :=
  #[s[k]![S[0]!]!]

@[expose] def hnfStabCore (tA tAi tB tBi g1 g1i g2 g2i : Array Nat) : Bool :=
  let G := #[tA, g1, g2]
  let Ginv := #[tAi, g1i, g2i]
  let beta := hnfRepTab #[tA, tB] #[tAi, tBi] hnfRepWords[8]!
  let s := hnfStabWords.map fun w => pword hnfN G Ginv w
  hnfTabsOK tA tAi tB tBi g1 g1i g2 g2i && s.size == 2 &&
    s.all (fun t => peq hnfN (pcomp hnfN t beta) (pcomp hnfN beta t)) &&
    (hnfWalk 2 (hnfPtStep s) (fun S => S[0]!) (hnfDecodeMoves hnfStabMovesStr) [#[hnfStabSeed]]
      ((∅ : Std.HashSet Nat).insert hnfStabSeed) 1 == some hnfStabN)

@[noinline, expose] def hnfStabCheck (B : ByteArray) : Bool :=
  let tA := hnfArch B 0
  let tB := hnfArch B 1
  let tAi := pinvCand hnfN tA
  let tBi := pinvCand hnfN tB
  let g1 := pword hnfN #[tA, tB] #[tAi, tBi] hnfW1
  let g2 := pword hnfN #[tA, tB] #[tAi, tBi] hnfW2
  hnfStabCore tA tAi tB tBi g1 (pinvCand hnfN g1) g2 (pinvCand hnfN g2)

end CFSG.EvenSporadicStandard.Solomon78
