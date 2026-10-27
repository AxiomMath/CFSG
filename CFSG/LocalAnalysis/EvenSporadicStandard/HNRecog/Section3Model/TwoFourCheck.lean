module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableICheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def tfComm : List (List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  [([(1, 3), (2, 2), (1, 1)], [(2, 3), (1, 2), (2, 2), (1, 1)], [(1, 1), (2, 4), (1, 1)]),
    ([(1, 3), (2, 1)], [(1, 5), (2, 3), (1, 2), (2, 1)], [(1, 3), (2, 4), (1, 1)])]

@[expose] def tfCap : ℕ := 100

@[expose] def orbGenOK (cap : ℕ) (kg : List (List ℕ)) (m : ℕ) (x : Table) : Bool :=
  let pg := p0Tabs kg
  let pgInv := p0Invs kg
  let o := conjClosureH 1408 pg pgInv x cap
  let S := mulClosureH 1408 o.1 cap
  conjTreeOK 1408 pg pgInv x o.1 o.2.1 o.2.2 && mulTreeOK 1408 o.1 S.1 S.2.1 S.2.2 &&
    hkeysDistinct 1408 S.1.toList && S.1.size == m

@[expose] def twoFourOK : Bool :=
  let cg := classz₁.centGens
  gensOK && cg.all wordOK && cg.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) &&
    tfComm.map (fun p => p.2.2) == sSpec3 &&
    tfComm.all (fun p => commutatorEqOK (tabW (specWord cg p.1)) (tabW (specWord cg p.2.1))
      (tabW (specWord cg p.2.2))) &&
    (subgroupList capI nWords3).all (fun t => tblEq 1408 t (idT 1408) || orbGenOK tfCap cg 16 t)

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
