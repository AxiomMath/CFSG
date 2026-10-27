module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenData
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenData

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative

set_option compiler.extract_closed false

@[expose] def centTableChecks (st : BFSState) (n c : Nat) (Z X Y Z0 Z1 : Array V4)
    (zT xT yT yiT z0T z1T : Table) (q0 : Table × Table × Table) : Bool :=
  matTableOK st (frTable (transposeRows Z)) zT n c &&
    matTableOK st (frTable (transposeRows X)) xT n c &&
    matTableOK st (frTable (transposeRows Y)) yT n c &&
    matTableOK st (frTable (transposeRows Z0)) z0T n c &&
    matTableOK st (frTable (transposeRows Z1)) z1T n c &&
    invOK n yT yiT &&
    treeOK n q0Size 1 q0.1 q0.2.1 (ap q0.2.2) xT yT

@[expose] def centPlaneChecks (n p0 bound : Nat) (zT xT yiT z0T z1T alphaT betaInvT gpl : Table)
    (q0 : Table × Table × Table) : Bool :=
  let r := stripZ zT gpl alphaT betaInvT q0.2.1 q0.2.2 xT yiT p0
  let qw := smallBFS r.2[2]! 60 z0T z1T
  decide (p0 < n) && decide (r.1 < q0Size) && r.2[0]! == 0 && r.2[1]! == 1 &&
    treeOK n q1Size r.2[2]! qw.1 qw.2 (findPt qw.1) z0T z1T &&
    decide (countAccept zT gpl alphaT betaInvT q0.2.1 q0.2.2 xT yiT qw.1 q1Size n 1048576 ≤ bound)

@[expose] def centCheckMulti (Z : Array V4) (bound c lo k : Nat) : Bool :=
  let st := thBFS ()
  let n := st.count
  let alphaT := tblOfBytes n st.alpha
  let betaT := tblOfBytes n st.beta
  let gpl := tblOfBytes n st.par
  let betaInvT := invT n betaT
  let X := xRows ()
  let Y := yRows ()
  let Z0 := z0Rows ()
  let Z1 := z1Rows ()
  let zT := matTable st (frTable (transposeRows Z)) n c
  let xT := matTable st (frTable (transposeRows X)) n c
  let yT := matTable st (frTable (transposeRows Y)) n c
  let yiT := invT n yT
  let z0T := matTable st (frTable (transposeRows Z0)) n c
  let z1T := matTable st (frTable (transposeRows Z1)) n c
  let q0 := localBFS n 1 xT yT
  centTableChecks st n c Z X Y Z0 Z1 zT xT yT yiT z0T z1T q0 &&
    (List.range k).any fun i =>
      centPlaneChecks n (lo + i) bound zT xT yiT z0T z1T alphaT betaInvT gpl q0

@[expose] def thSevenOK (c : Nat) : Bool :=
  let regs := slpRows (rowsOf seedA) (rowsOf seedB) 43 prog7
  let X := regs[24]!
  let Y := regs[25]!
  let Z := mulRows X (powRowsN Y 6)
  prog7.all (Op.lt 43) && pairOK X Y 7 && conjOK regs X Y Z 7 conj7 &&
    coreListOK regs Z list7 && centCheckMulti Z 1176 c 0 10000

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
