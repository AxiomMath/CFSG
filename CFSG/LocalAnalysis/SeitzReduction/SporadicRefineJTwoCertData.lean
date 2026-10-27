module

public import CFSG.Sporadic.SmallOddCore.J2Data

public section

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

@[expose] def j2SylEnum : Array Table := (mulClosureH 315 j2SylowGenTbls.toArray 3000).1

@[expose] def j2EAIdxOne : List ℕ := [0, 1, 2, 3, 4, 9, 10, 11, 16, 17, 22, 54, 55, 59, 84, 138]

@[expose] def j2EAIdxTwo : List ℕ :=
  [0, 5, 6, 17, 35, 54, 59, 66, 71, 89, 91, 92, 96, 173, 210, 215]

@[expose] def movedCount (n : ℕ) (T : Table) : ℕ := (List.range n).countP fun i => ap T i != i

@[expose] def idxClosedOK (n : ℕ) (E : Array Table) (I : List ℕ) : Bool :=
  I.all (· < E.size) &&
    I.all fun y => I.all fun z => I.any fun t => tblEq n (compT n E[y]! E[z]!) E[t]!

@[expose] def centInvolIdx (n : ℕ) (sift : Table → Bool) (E : Array Table) (i : ℕ) : List ℕ :=
  (List.range E.size).filter fun y => sift E[y]! && invoOK n E[y]! && commTT n E[y]! E[i]!

@[expose] def eaCountOK (n : ℕ) (sift : Table → Bool) (E : Array Table) (I₁ I₂ : List ℕ) : Bool :=
  (List.range E.size).all fun i =>
    I₁.contains i || I₂.contains i || !sift E[i]! || !invoOK n E[i]! ||
      decide ((centInvolIdx n sift E i).length < 16)

@[expose] def idxNormOK (n : ℕ) (E : Array Table) (m : ℕ) (I : List ℕ) : Bool :=
  I.all fun y => I.any fun t => tblEq n (compT n E[m]! E[y]!) (compT n E[t]! E[m]!)

@[expose] def twoSupportsOK (n : ℕ) (E : Array Table) (m : ℕ) (I : List ℕ) : Bool :=
  I.any fun a => I.any fun b =>
    commTT n E[a]! E[m]! && commTT n E[b]! E[m]! && !tblEq n E[a]! (idT n) &&
      !tblEq n E[b]! (idT n) && movedCount n E[a]! != movedCount n E[b]!

@[expose] def eaSupportOK (n : ℕ) (sift : Table → Bool) (E : Array Table) (I₁ I₂ : List ℕ) :
    Bool :=
  (List.range E.size).all fun m =>
    sift E[m]! || !involOK n E[m]! ||
      [I₁, I₂].all fun I => !idxNormOK n E m I || twoSupportsOK n E m I

end CFSG.SeitzReduction.SporadicRefine
