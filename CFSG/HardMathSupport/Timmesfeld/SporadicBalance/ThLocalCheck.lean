module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporThE81Data
public import Certificates.Data.CFSGNative.Timmesfeld.ThCent

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal

open CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Fischer

@[expose] def matOf (P : Array Mat) (par lab : Array ℕ) : ℕ → ℕ → Mat
  | 0, _ => idRows
  | f + 1, i => if i = 0 then idRows else mulRows P[lab[i]!]! (matOf P par lab f par[i]!)

@[expose] def thLocalChecks (E : ThE81Data) (X : ThLocalData) (A B Z : Mat) (gs P : Array Mat)
    (c : ArrCert) : Bool :=
  let tabs := tabsOf P
  let M := matOf P c.par c.lab qN
  let gs4 : Array Mat := #[A, B, gs[0]!, gs[1]!]
  E.w61.all (fun x => decide (x.1 < 2)) && E.w62.all (fun x => decide (x.1 < 2)) &&
    E.pW.toList.all (fun w => w.all fun x => decide (x.1 < 2)) &&
    pcCheck 10 P E.cubeW E.commW &&
    CFSG.RankThree.PartTwo.Sec4.Item434SporTh.orbitOK tabs E.v c qN &&
    localTableChecks c.edges c.par c.lab X &&
    X.fus.all (fun f => X.reps.contains f.1 && decide (f.2.1 < qN) &&
      f.2.2.all (fun x => decide (x.1 < 4)) &&
      X.tgts.any (fun y => y.1 == f.2.1) &&
      mulRows (evalWord gs4 f.2.2) (M f.1) == mulRows (M f.2.1) (evalWord gs4 f.2.2)) &&
    X.reps.all (fun r => X.fus.any (fun f => f.1 == r) || X.tgts.any (fun y => y.1 == r)) &&
    X.invW.all (fun x => decide (x.1 < 4)) &&
    decide (X.invPos.1 < 248) && decide (X.invPos.2 < 248) &&
    mulRows (evalWord gs4 X.invW) (evalWord gs4 X.invW) == idRows &&
    ((evalWord gs4 X.invW)[X.invPos.1]?.getD V4.zero).testBit X.invPos.2 !=
      (X.invPos.1 == X.invPos.2) &&
    mulRows (evalWord gs4 X.invW) (M 10) == mulRows (M 10) (evalWord gs4 X.invW) &&
    M 10 == Z

@[expose] def thLocalCheck (X : ThLocalData) (A B : Mat) : Bool :=
  let gs : Array Mat := #[evalWord #[A, B] thE81.w61, evalWord #[A, B] thE81.w62]
  let P : Array Mat := thE81.pW.map (evalWord gs)
  thLocalChecks thE81 X A B (zRows ()) gs P (orbCert (tabsOf P) thE81.v thE81.fuel)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal
