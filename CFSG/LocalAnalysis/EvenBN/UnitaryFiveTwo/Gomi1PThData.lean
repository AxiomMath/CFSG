module

public import Certificates.Data.CFSGNative.SectionRank.Th

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.SectionRank.Native

@[expose] def ord8OK {M V : Type} [Inhabited M] (O : Ops M V) (D : Data) (r k : Nat) : Bool :=
  let R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs)
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (r < D.nregs) &&
    O.eq (O.pow R[r]! 8) O.one && O.vne (O.vmul (O.unit k) (O.pow R[r]! 4)) (O.unit k)

@[expose] def thOrd8Data : Data where
  seedA := thData.seedA
  seedB := thData.seedB
  nregs := 12
  prog := [.pow 2 1 2, .mul 0 1 3, .mul 0 2 4, .mul 3 3 5, .mul 5 3 6, .mul 6 4 7, .mul 7 3 8,
    .mul 8 4 9, .mul 9 4 10, .pow 3 10 11]
  outs := [11]
  tests := [0]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
