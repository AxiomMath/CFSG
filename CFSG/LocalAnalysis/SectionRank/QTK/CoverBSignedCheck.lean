module

public import CFSG.RankThree.PartTwo.Census.Sporadic.FourGroupCert

public section

namespace CFSG.SectionRank.QTK.CoverB

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census

structure SignedData where
  base : Data
  t₁ : ℕ
  t₂ : ℕ
  a : ℕ
  b : ℕ
  d₁ : ℕ
  d₂ : ℕ

namespace SignedData

variable {M V : Type} (O : Ops M V)

@[expose] def check [Inhabited M] (D : SignedData) : Bool :=
  let R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  let T₁ := R[D.t₁]!
  let T₂ := R[D.t₂]!
  let A := R[D.a]!
  let B := R[D.b]!
  let D₁ := R[D.d₁]!
  let D₂ := R[D.d₂]!
  D.base.prog.all (Op.lt D.base.nregs) &&
    [D.t₁, D.t₂, D.a, D.b, D.d₁, D.d₂].all (decide <| · < D.base.nregs) &&
    O.elemOK [A, B] D.base.tests &&
    O.eq (O.mul T₁ T₁) O.one && O.eq (O.mul T₂ T₂) O.one && O.commOK T₁ T₂ &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) T₁) (O.unit k)) &&
    V4Data.conjOK O A T₁ T₁ T₂ && V4Data.conjOK O A T₂ T₁ T₂ &&
    V4Data.conjOK O B T₁ T₁ T₂ && V4Data.conjOK O B T₂ T₁ T₂ &&
    O.eq (O.mul D₁ D₁) O.one && O.eq (O.mul D₂ D₂) O.one &&
    O.eq (O.mul D₁ A) (O.mul (O.mul A A) D₁) && O.commOK D₁ B &&
    O.eq (O.mul D₂ B) (O.mul (O.mul B B) D₂)

end SignedData

end CFSG.SectionRank.QTK.CoverB
