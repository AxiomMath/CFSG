module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockCheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

structure OrbRow where
  conj : List ℕ
  m : ℕ
  n : ℕ
  stab : List (List (ℕ × ℕ))

@[expose] def OrbRow.stabWords (kg : List (List ℕ)) (r : OrbRow) : List (List ℕ) :=
  r.stab.map (specWord kg)

@[expose] def OrbRow.repTab (wy : List ℕ) (r : OrbRow) : Table :=
  conjTab r.conj (tabW wy)

@[expose] def orbRowOK (cap : ℕ) (kg : List (List ℕ)) (wy : List ℕ) (korder : ℕ) (r : OrbRow) :
    Bool :=
  let pg := p0Tabs kg
  let pgInv := p0Invs kg
  let c := r.repTab wy
  let o := conjClosureH 1408 pg pgInv c cap
  let sg := p0Tabs (r.stabWords kg)
  let S := mulClosureH 1408 sg cap
  gensOK && wordOK wy && wordOK r.conj && kg.all wordOK &&
    kg.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) &&
    invOK 1408 (tabW r.conj) (invT 1408 (tabW r.conj)) &&
    conjTreeOK 1408 pg pgInv c o.1 o.2.1 o.2.2 && hkeysDistinct 1408 o.1.toList &&
    o.1.size == r.m && commWordsOK (r.stabWords kg) c &&
    mulTreeOK 1408 sg S.1 S.2.1 S.2.2 && hkeysDistinct 1408 S.1.toList && S.1.size == r.n &&
    r.m * r.n == korder

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
