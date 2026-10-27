
module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

@[expose] def invCentN (n : ℕ) (L : List (Array ℕ)) (t : Array ℕ) : List (Array ℕ) :=
  L.filter fun a => commN n a t && eqA n (mulN n a a) (idA n) && !(eqA n a (idA n))

@[expose] def noE8N (n : ℕ) (I : List (Array ℕ)) : Bool :=
  I.all fun a => I.all fun b => I.all fun c =>
    !(commN n a b && commN n a c && commN n b c) || eqA n b a || eqA n c a || eqA n c b ||
      eqA n c (mulN n a b)

@[expose] def orbitW (n : ℕ) (T M : List (Array ℕ)) (t0 : Array ℕ) (W : List ℕ) : Bool :=
  (List.range T.length).all fun i => eqA n T[i]! (idA n) ||
    (decide (W[i]! < M.length) && eqA n (conjA n M[W[i]!]! T[i]!) t0) ||
    noE8N n (invCentN n M T[i]!)

@[expose] def moveN (n : ℕ) (M gs rs R : List (Array ℕ)) : Bool :=
  M.all fun m => gs.any fun g => rs.any fun r =>
    !(inLN n R (conjInvA n m (conjA n g (conjA n m r))))

@[expose] def normalE8N (n : ℕ) (T C N : List (Array ℕ)) (t0 : Array ℕ) : Bool :=
  (invCentN n C t0).all fun a => inLN n N a || T.any fun t =>
    !(eqA n t (idA n)) && !(eqA n t t0) &&
      (invCentN n C t0).all fun b => !(commN n a b) || commN n b t

@[expose] def blockN (n k : ℕ) (C : List (Array ℕ)) (blk rep : Array ℕ) : Bool :=
  (List.range k).all (fun i => decide (rep[i]! < n) && blk[rep[i]!]! == i) &&
    C.all fun t => (List.range n).all fun v => !(decide (blk[v]! < k)) ||
      (decide (blk[t[v]!]! < k) && blk[t[v]!]! == blk[t[rep[blk[v]!]!]!]!)

@[expose] def faithfulN (n : ℕ) (C : List (Array ℕ)) (blk rep : Array ℕ) (k : ℕ)
    (blk' rep' : Array ℕ) (k' : ℕ) : Bool :=
  C.all fun t => !((List.range k).all fun i => blk[t[rep[i]!]!]! == i) ||
    !((List.range k').all fun i => blk'[t[rep'[i]!]!]! == i) || eqA n t (idA n)

@[expose] def fuseW (n : ℕ) (T M N : List (Array ℕ)) (t0 : Array ℕ) (F : ℕ × ℕ × ℕ) : Bool :=
  decide (F.1 < N.length) && decide (F.2.1 < T.length) && decide (F.2.2 < M.length) &&
    !(eqA n (commutatorA n N[F.1]! T[F.2.1]!) (idA n)) &&
    !(eqA n (commutatorA n N[F.1]! T[F.2.1]!) t0) &&
    eqA n (conjA n M[F.2.2]! (commutatorA n N[F.1]! T[F.2.1]!)) t0

@[expose] def hexaCheck : Bool :=
  let T := eltsN 64 hexaTGens
  let M := eltsN 64 hexaMGens
  let C := eltsN 64 hexaCGens
  let N := eltsN 64 hexaN0Gens
  let R := eltsN 64 hexaR0Gens
  enumCheckN 64 hexaTGens 64 && enumCheckN 64 hexaMGens 2160 && enumCheckN 64 hexaCGens 48 &&
    enumCheckN 64 hexaN0Gens 8 && enumCheckN 64 hexaR0Gens 4 && validA 64 hexaT0 &&
    hexaR0Gens.all (inLN 64 T) &&
    hexaMGens.all (fun g => hexaTGens.all fun q => inLN 64 T (conjA 64 g q)) &&
    orbitW 64 T M hexaT0 hexaOrbConj &&
    hexaCGens.all (inLN 64 M) && hexaCGens.all (fun g => commN 64 g hexaT0) &&
    (M.filter fun m => commN 64 m hexaT0).length == 48 &&
    hexaCGens.all (fun g => eqA 64 (powN 64 g 4) (idA 64)) &&
    moveN 64 M hexaCGens hexaR0Gens R &&
    hexaCGens.all (fun g => hexaN0Gens.all fun q => inLN 64 N (conjA 64 g q)) &&
    normalE8N 64 T C N hexaT0 &&
    blockN 64 4 C hexaBlk4 hexaRep4 && blockN 64 2 C hexaBlk2 hexaRep2 &&
    faithfulN 64 C hexaBlk4 hexaRep4 4 hexaBlk2 hexaRep2 2 && fuseW 64 T M N hexaT0 hexaFuseW

end CFSG.ComponentClassification.AS81.Hexa
