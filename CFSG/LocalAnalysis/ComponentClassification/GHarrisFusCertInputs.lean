module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs

public section

namespace CFSG.ComponentClassification.GHarris.SCert

@[expose] def SE.allList : List SE :=
  (List.finRange 8).flatMap fun d => (List.finRange 4).flatMap fun a =>
    (List.finRange 4).flatMap fun b => (List.finRange 4).map fun c => SE.mk d a b c

@[expose] def SE.enc (s : SE) : Nat := s.d.val * 64 + s.v0.val * 16 + s.v1.val * 4 + s.v2.val

@[expose] def SE.dec (n : Nat) : SE :=
  ⟨Fin.ofNat 8 (n / 64), ((n / 16 : ℕ) : ZMod 4), ((n / 4 : ℕ) : ZMod 4), ((n : ℕ) : ZMod 4)⟩

@[expose] def SE.clsArr : Array Nat :=
  #[0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 3, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 5, 0, 0, 0, 0, 0, 3, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0,
    0, 5, 0, 3, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 5, 0, 0, 0, 0, 0, 3, 0, 0, 0, 5, 0, 0, 0, 3, 0,
    0, 0, 5, 0, 4, 0, 0, 0, 0, 6, 0, 0, 0, 0, 4, 0, 0, 0, 0, 6, 0, 0, 4, 0, 0, 0, 0, 6, 4, 0, 0,
    0, 0, 6, 0, 0, 4, 0, 0, 0, 0, 6, 0, 0, 0, 0, 4, 0, 0, 0, 0, 6, 0, 0, 4, 0, 0, 0, 0, 6, 4, 0,
    0, 0, 0, 6, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 4,
    0, 4, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0,
    4, 0, 4, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 8, 0, 0, 0, 0, 0, 8,
    0, 8, 0, 0, 0, 0, 0, 8, 0, 7, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 8, 0, 0, 0, 0, 0,
    8, 0, 8, 0, 0, 0, 0, 0, 8, 0, 7, 0, 0, 0, 8, 0, 0, 0, 7, 0, 0, 0, 8, 0, 0, 0, 8, 0, 0, 0, 7,
    0, 0, 0, 8, 0, 0, 0, 7, 0, 0, 0, 7, 0, 0, 0, 8, 0, 0, 0, 7, 0, 0, 0, 8, 0, 0, 0, 8, 0, 0, 0,
    7, 0, 0, 0, 8, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def SE.clsTab (s : SE) : Nat := SE.clsArr.getD s.enc 0

@[expose] def SE.isInvB (s : SE) : Bool := s * s == 1 && s != 1

@[expose] def SE.clsOk : Bool :=
  SE.allList.all fun s => !(SE.isInvB s) || (decide (SE.clsTab s < 9) &&
    SE.allList.any fun c => c⁻¹ * s * c == SE.invRep (Fin.ofNat 9 (SE.clsTab s)))

@[expose] def SE.mulArr : Array SE :=
  Array.ofFn (n := 262144) fun i => SE.dec (i.val / 512) * SE.dec (i.val % 512)

@[expose] def SE.fmul (T : Array SE) (a b : SE) : SE := T.getD (a.enc * 512 + b.enc) 1

namespace Fus

variable (mul : SE → SE → SE)

@[expose] def isInv (s : SE) : Bool := mul s s == 1 && s != 1

@[expose] def evalW (q : Array SE) (w : List Nat) : SE :=
  w.foldl (fun acc i => mul acc (q.getD i 1)) 1

@[expose] def pat (q : Array SE) (i j : Nat) : Bool × Bool × Bool × Bool :=
  let p := mul (q.getD i 1) (q.getD j 1)
  let p2 := mul p p
  (p == 1, p2 == 1, mul p2 p2 == 1, p == mul (q.getD j 1) (q.getD i 1))

end Fus

structure Fus.Data where
  source : SE
  gens : Array SE
  words : Array (List Nat)
  mulIdx : Array (Array Nat)
  target : SE
  zIdx : Nat
  badPairs : List (Nat × Nat)
  useE : Bool
  useF : Bool
  good : (SE → SE → SE) → Array SE → Bool

namespace Fus.Data

variable (mul : SE → SE → SE) (A : Data)

@[expose] def elt (k : Nat) : SE := Fus.evalW mul A.gens (A.words.getD k [])

@[expose] def img (q : Array SE) (k : Nat) : SE := Fus.evalW mul q (A.words.getD k [])

@[expose] def mi (k i : Nat) : Nat := (A.mulIdx.getD k #[]).getD i 0

@[expose] def pairOk (q : Array SE) (i j : Nat) : Bool :=
  Fus.pat mul q i j == Fus.pat mul A.gens i j

@[expose] def condB (q : Array SE) : Bool :=
  let im := (List.range 32).toArray.map (A.img mul q)
  (List.range 32).all (fun k => (List.range 4).all fun i =>
    im.getD (A.mi k i) 1 == mul (im.getD k 1) (q.getD i 1)) &&
    (List.range 32).all (fun k => k == 0 || im.getD k 1 != 1)

@[expose] def hasEdge (q : Array SE) (i j : Nat) : Bool :=
  (List.range 32).any fun k =>
    Fus.isInv mul (A.elt mul k) && SE.clsTab (A.elt mul k) == i && SE.clsTab (A.img mul q k) == j

@[expose] def badB (q : Array SE) : Bool :=
  (List.range 32).any fun k =>
    Fus.isInv mul (A.elt mul k) &&
      A.badPairs.contains (SE.clsTab (A.elt mul k), SE.clsTab (A.img mul q k))

@[expose] def fixZ (q : Array SE) : Bool := A.img mul q A.zIdx == SE.gen 0

@[expose] def badEB (q : Array SE) : Bool :=
  A.useE && A.fixZ mul q && (List.range 32).any fun k =>
    decide (SE.predE (A.elt mul k)) != decide (SE.predE (A.img mul q k))

@[expose] def badFB (q : Array SE) : Bool :=
  A.useF && A.fixZ mul q && (List.range 32).any fun k =>
    decide (SE.predF (A.elt mul k)) != decide (SE.predF (A.img mul q k))

@[expose] def outB (q : Array SE) : Bool :=
  A.badB mul q || A.badEB mul q || A.badFB mul q || A.good mul q

@[expose] def tableOk : Bool :=
  A.gens.size == 4 && A.words.size == 32 && A.mulIdx.size == 32 &&
    A.mulIdx.all (fun r => r.size == 4 && r.all fun j => decide (j < 32)) &&
    A.words.all (fun w => w.all fun i => decide (i < 4)) && A.zIdx < 32 &&
    A.gens.getD 0 1 == A.source && (List.range 4).all (fun i => Fus.isInv mul (A.gens.getD i 1) &&
      mul (A.gens.getD i 1) A.source == mul A.source (A.gens.getD i 1)) &&
    (List.range 32).all (fun k => (List.range 4).all fun i =>
      A.elt mul (A.mi k i) == mul (A.elt mul k) (A.gens.getD i 1)) &&
    A.words.getD 0 [0] == [] && (List.range 32).all (fun k => k == 0 || A.elt mul k != 1) &&
    A.elt mul A.zIdx == SE.gen 0

@[expose] def checkM : Bool :=
  let invs := SE.allList.filter (Fus.isInv mul)
  A.tableOk mul && invs.all fun q1 =>
    !(A.pairOk mul #[A.target, q1, 1, 1] 0 1) || invs.all fun q2 =>
      !(A.pairOk mul #[A.target, q1, q2, 1] 0 2 && A.pairOk mul #[A.target, q1, q2, 1] 1 2) ||
        invs.all fun q3 =>
          !(A.pairOk mul #[A.target, q1, q2, q3] 0 3 && A.pairOk mul #[A.target, q1, q2, q3] 1 3 &&
              A.pairOk mul #[A.target, q1, q2, q3] 2 3) ||
            !(A.condB mul #[A.target, q1, q2, q3]) || A.outB mul #[A.target, q1, q2, q3]

end Fus.Data

@[expose] def Fus.checkList (L : List Fus.Data) : Bool :=
  let T := SE.mulArr
  L.all fun A => A.checkM (SE.fmul T)

end CFSG.ComponentClassification.GHarris.SCert
