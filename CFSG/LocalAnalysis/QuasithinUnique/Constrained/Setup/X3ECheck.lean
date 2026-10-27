module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Chain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EData

public section

namespace CFSG.QuasithinUnique.Setup.X3E

set_option maxRecDepth 100000

@[expose] def piCols (tau : List Nat) : List Nat := (List.range 45).map fun i => 1 <<< tau.getD i 0

@[expose] def colsOf (b : Bool) : List Nat := if b then eMy else eMx

@[expose] def piColsOf (b : Bool) : List Nat := piCols (if b then eTauY else eTauX)

@[expose] def baseOK : Bool :=
  eB.length == 45 && eT.length == 45 && eMx.length == 45 && eMy.length == 45 &&
    (List.range 45).all (fun i => papply 45 eB (eT.getD i 0) == 1 <<< i) &&
    (List.range 45).all (fun j => papply 45 eB (colsOf false |>.getD j 0) ==
      papply 45 (piColsOf false) (eB.getD j 0)) &&
    (List.range 45).all (fun j => papply 45 eB (colsOf true |>.getD j 0) ==
      papply 45 (piColsOf true) (eB.getD j 0))

@[expose] def flagOK : Bool :=
  eNs.length == 13 && eNs.getD 0 0 == 0 && eNs.getD 12 0 == 45 &&
    (List.range 12).all (fun i => eNs.getD i 0 < eNs.getD (i + 1) 0) &&
    (List.range 13).all fun i => (List.range (eNs.getD i 0)).all fun j =>
      eMx.getD j 0 < 2 ^ eNs.getD i 0 && eMy.getD j 0 < 2 ^ eNs.getD i 0

@[expose] def blkOf (i : Nat) (b : Bool) : List Nat :=
  blkCols (colsOf b) (eNs.getD i 0) (eNs.getD (i + 1) 0 - eNs.getD i 0)

@[expose] def blocksOK : Bool :=
  eAW.length == 12 && eKers.length == 12 && ePsi.length == 12 && eDw.length == 12 &&
    eRc.length == 12 && eMinv.length == 12 &&
    (List.range 12).all fun i =>
      nortonOK (eNs.getD (i + 1) 0 - eNs.getD i 0) (blkOf i) (eAW.getD i []) (eKers.getD i [])
        (ePsi.getD i 0) (eDw.getD i []) (eRc.getD i []) (eMinv.getD i [])

@[expose] def dimsOK : Bool :=
  (List.range 12).all fun i =>
    let d := eNs.getD (i + 1) 0 - eNs.getD i 0
    d == 1 || d == 4 || d == 16

@[expose] def fixOK : Bool :=
  (List.range 12).all fun i =>
    let d := eNs.getD (i + 1) 0 - eNs.getD i 0
    d != 4 || ((List.range 16).filter fun t => eR0W.all fun w => wapp 4 (blkOf i) w t == t).length == 2

theorem baseOK_true : baseOK = true := by decide +kernel

theorem flagOK_true : flagOK = true := by decide +kernel

theorem dimsOK_true : dimsOK = true := by decide +kernel

theorem fixOK_true : fixOK = true := by decide +kernel

theorem blocksOK_true : blocksOK = true := by decide +kernel

end CFSG.QuasithinUnique.Setup.X3E
