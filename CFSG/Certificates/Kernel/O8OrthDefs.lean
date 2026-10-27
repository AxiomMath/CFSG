module

public import CFSG.Certificates.Kernel.O8SoundDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainInvData

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

@[expose] def extendColsG (q : ℕ → Bool) (cs : List ℕ) : List ℕ :=
  (List.range 64).filter fun c => q c == q (2 ^ cs.length) &&
    (List.range cs.length).all fun i => bfG q (cs.getD i 0) c == bfG q (2 ^ i) (2 ^ cs.length)

@[expose] def oColsAuxG (q : ℕ → Bool) : ℕ → List ℕ → List (List ℕ)
  | 0, cs => [cs]
  | m + 1, cs => (extendColsG q cs).flatMap fun c => oColsAuxG q m (cs ++ [c])

@[expose] def oColsG (q : ℕ → Bool) : List (List ℕ) := oColsAuxG q 6 []

@[expose] def invCheckG (q : ℕ → Bool) : Bool :=
  (oColsG q).all fun C => dickC C || !isInvol C || fixCount C == 16

@[expose] def wordActG (G : ℕ → Array ℕ) : List ℕ → ℕ → ℕ
  | [], x => x
  | i :: w, x => bmulVec 6 6 (G i) (wordActG G w x)

@[expose] def genCheckG (q : ℕ → Bool) (G GI : ℕ → Array ℕ) : Bool :=
  (List.range 6).all fun i =>
    bIsId 6 (bmul 6 6 (G i) (GI i)) && bIsId 6 (bmul 6 6 (GI i) (G i)) &&
      (List.range 64).all fun x => q (bmulVec 6 6 (G i) x) == q x

@[expose] def orbitCheckG (q : ℕ → Bool) (G : ℕ → Array ℕ) (OW : Array (List ℕ)) (n : ℕ) :
    Bool :=
  (List.range 64).all fun x => x == 0 || wordActG G (OW.getD x []) (if q x then n else 1) == x

@[expose] def dickCheckG (q : ℕ → Bool) (G GI : ℕ → Array ℕ) : Bool :=
  (oColsG q).all fun C => dickC C ||
    (List.range 6).all fun i => !dickC (C.map (bmulVec 6 6 (G i))) &&
      !dickC (C.map (bmulVec 6 6 (GI i)))

@[expose] def coneCheckG (q : ℕ → Bool) (X Xi Y Yi : Array ℕ × ℕ) (C : List ℕ) : Bool :=
  let comm := fun v => affB X (affB Y (affB Xi (affB Yi v)))
  ((List.range 64).all fun v =>
    q (affB X v) == q v && q (affB Y v) == q v &&
      affB Xi (affB X v) == v && affB X (affB Xi v) == v &&
      affB Yi (affB Y v) == v && affB Y (affB Yi v) == v) &&
    ((List.range 6).all fun j => comm (2 ^ j) == C.getD j 0) && comm 0 == 0 && dickC C

end CFSG.KC.O8

end
