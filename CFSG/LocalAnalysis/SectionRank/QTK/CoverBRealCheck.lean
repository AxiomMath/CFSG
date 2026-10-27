module

public import CFSG.RankThree.PartTwo.Census.Sporadic.FourGroupCert

public section

namespace CFSG.SectionRank.QTK.CoverB

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census

structure RealData where
  base : Data
  t₁ : ℕ
  t₂ : ℕ
  x : ℕ
  d : ℕ
  a : ℕ
  b : ℕ
  dord : ℕ

namespace RealData

variable {M V : Type} (O : Ops M V)

@[expose] def localOK (D : RealData) (T₁ T₂ X Dd : M) : Bool :=
  O.eq (O.mul T₁ T₁) O.one && O.eq (O.mul T₂ T₂) O.one && O.commOK T₁ T₂ &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) T₁) (O.unit k)) &&
    V4Data.conjOK O X T₁ T₁ T₂ && V4Data.conjOK O X T₂ T₁ T₂ && O.cubeOK X &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) X) (O.unit k)) &&
    decide (0 < D.dord) && O.eq (O.pow Dd D.dord) O.one &&
    O.eq (O.mul Dd X) (O.mul (O.mul X X) Dd)

@[expose] def checkElem [Inhabited M] (D : RealData) : Bool :=
  let R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  D.base.prog.all (Op.lt D.base.nregs) &&
    [D.t₁, D.t₂, D.x, D.d].all (decide <| · < D.base.nregs) &&
    localOK O D R[D.t₁]! R[D.t₂]! R[D.x]! R[D.d]!

end RealData

end CFSG.SectionRank.QTK.CoverB
