module

public import CFSG.CGT.T75JM.Interfaces

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Mathieu.Native

@[expose] def m22EnumPD : Bool := subsetCheck m22RelsPD [0, 1, 2, 3, 4, 5] 200000 77

@[noinline, expose] def thetaTabCheck : Bool :=
  let T0 := m22Img 0
  let T1 := m22Img 1
  let T2 := m22Img 2
  let T3 := m22Img 3
  let T4 := m22Img 4
  let T5 := m22Img 5
  let T6 := m22Img 6
  let V0 := invT 22 T0
  let V1 := invT 22 T1
  let V2 := invT 22 T2
  let V3 := invT 22 T3
  let V4 := invT 22 T4
  let V5 := invT 22 T5
  let V6 := invT 22 T6
  thetaRels.all fun r =>
    wordT 22 (m22ImgLetter T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6) (r.map m22LetterZ) ==
      idT 22

end CFSG.CGT.T75JM
