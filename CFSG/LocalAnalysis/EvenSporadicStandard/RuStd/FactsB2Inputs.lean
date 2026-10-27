module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public import CFSG.Sporadic.Schreier.RuCheckInvInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowFour
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public meta import CFSG.Sporadic.Schreier.RuCheckInvInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
public meta import CFSG.Walter.JRFacts

public section

namespace CFSG.EvenSporadicStandard.RuStd

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.TwoRu.HypOne CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def conjClosedH (n : ℕ) (gens gensInv L : Array Table) : Bool :=
  let idx := hashIndex n L
  L.all fun x => (List.range gens.size).all fun l =>
    memTH n L idx (conjT n gens[l]! gensInv[l]! x) &&
      memTH n L idx (conjT n gensInv[l]! gens[l]! x)

@[expose] def classCheckOf (n : ℕ) (gens gensInv : Array Table) (r : Table)
    (q : Array Table × Array ℕ × Array ℕ) (N : ℕ) : Bool :=
  conjTreeOK n gens gensInv r q.1 q.2.1 q.2.2 && conjClosedH n gens gensInv q.1 &&
    hkeysDistinct n q.1.toList && q.1.size == N

@[expose] def ruInvWord1 : List ℤ := [1, -2, 1, -2, 1, -2, 1, -2]

@[expose] def ruInvWord2 : List ℤ := [2, 2]

@[expose] def ruInvWord3 : List ℤ := [1, 2, 1, 2]

@[expose] def ruInvWord4 : List ℤ := [1, 1, 2, 1, -2, 1, 2]

@[expose] def ruInvRepOf (w : List ℤ) : Table := wordT 4060 (letterTab cGens cGensInv) w

@[expose] def ruInvRep0 : Table := tblOfArr ruZA

@[expose] def ruInvClOf (r : Table) : Array Table × Array ℕ × Array ℕ :=
  conjClosureH 4060 cGens cGensInv r 700

@[expose] def ruInvCl0 : Array Table × Array ℕ × Array ℕ := ruInvClOf ruInvRep0

@[expose] def ruInvCl1 : Array Table × Array ℕ × Array ℕ := ruInvClOf (ruInvRepOf ruInvWord1)

@[expose] def ruInvCl2 : Array Table × Array ℕ × Array ℕ := ruInvClOf (ruInvRepOf ruInvWord2)

@[expose] def ruInvCl3 : Array Table × Array ℕ × Array ℕ := ruInvClOf (ruInvRepOf ruInvWord3)

@[expose] def ruInvCl4 : Array Table × Array ℕ × Array ℕ := ruInvClOf (ruInvRepOf ruInvWord4)

@[expose] def ruInvAll : Array Table :=
  ruInvCl0.1 ++ ruInvCl1.1 ++ ruInvCl2.1 ++ ruInvCl3.1 ++ ruInvCl4.1

@[expose] def ruInvIdx : Std.HashMap UInt64 ℕ := hashIndex 4060 ruInvAll

@[expose] def ruInvCoverTest (t : Array ℕ) : Bool :=
  !(ruIsInvolA t && ruFixCount t == 92) || memTH 4060 ruInvAll ruInvIdx (tblOfArr t)

@[noinline, expose] def ruInvCheck : Bool :=
  classCheckOf 4060 cGens cGensInv ruInvRep0 ruInvCl0 1 &&
    classCheckOf 4060 cGens cGensInv (ruInvRepOf ruInvWord1) ruInvCl1 30 &&
    classCheckOf 4060 cGens cGensInv (ruInvRepOf ruInvWord2) ruInvCl2 240 &&
    classCheckOf 4060 cGens cGensInv (ruInvRepOf ruInvWord3) ruInvCl3 480 &&
    classCheckOf 4060 cGens cGensInv (ruInvRepOf ruInvWord4) ruInvCl4 640 &&
    all2 4060 ruLevS ruInvCoverTest

end CFSG.EvenSporadicStandard.RuStd
