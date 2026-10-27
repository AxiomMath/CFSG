module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def mmulL (p n : Nat) (A B : List Nat) : List Nat :=
  let Aa := A.toArray
  let Ba := B.toArray
  (List.range (n * n)).map fun idx =>
    ((List.range n).foldl
      (fun acc j => acc + Aa.getD (n * (idx / n) + j) 0 * Ba.getD (n * j + idx % n) 0) 0) % p

@[expose] def midL (p n : Nat) : List Nat :=
  (List.range (n * n)).map fun idx => if idx / n = idx % n then 1 % p else 0

@[expose] def mpowL (p n : Nat) (A : List Nat) : Nat → List Nat
  | 0 => midL p n
  | e + 1 => mmulL p n A (mpowL p n A e)

@[expose] def wordsL (p n : Nat) : List (List Nat) → List (List Nat)
  | [] => [midL p n]
  | A :: As => (wordsL p n As).flatMap fun M =>
      (List.range p).map fun a => mmulL p n (mpowL p n A a) M

@[expose] def codeL (p : Nat) (A : List Nat) : Nat := A.foldl (fun acc x => acc * p + x) 0

@[expose] def wChk (p n s : Nat) (L : List (List Nat)) : Bool :=
  let S := (L.map (codeL p)).mergeSort (fun a b => decide (a ≤ b))
  (S.zip S.tail).all (fun x => decide (x.1 < x.2)) && decide (p ^ s ≤ L.length * p ^ n)

@[expose] def NMod.wOK (p : Nat) (m : NMod) (tops : List Pc) (tidx : List Nat) (s : Nat) : Bool :=
  tidx.all (fun i => decide (i < m.acts.length) &&
    tops.any (·.reg == (m.acts.getD i default).reg)) &&
  wChk p m.basis.length s
    (wordsL p m.basis.length (tidx.map fun i => (m.acts.getD i default).mat))

@[expose] def NMod.modFactsW (p : Nat) (m : NMod) (tops : List Pc) : List MFact :=
  m.facts p ++ (tops ++ m.basisPc p).flatMap (Pc.facts p)

@[expose] def modCheckW {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (p : Nat) (m : NMod) (tops : List Pc) (tidx : List Nat) (s : Nat)
    (cf : Nat → Nat → Nat → Int) (ci : Nat → Nat → Nat → Nat → Nat → Int)
    (ct : Nat → Nat → Nat → Nat → Int) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, m.modFactsW p tops⟩ && m.wf p &&
  pcWf (tops ++ m.basisPc p) && tops.all (fun q => m.acts.any (·.reg == q.reg)) &&
  m.wOK p tops tidx s && decide (p ≤ m.basis.length) && m.funOK p cf && m.altOK p ci ct tgtAlt

end CFSG.AGLEmbedding.R3
