module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def invCap : Nat := 1000000

@[expose, noinline] def invCoverOK (a : Table) (Lz Laz Lb Lz₁ S : Array Table) : Bool :=
  S.all fun s =>
    !involOK 1408 s || tblEq 1408 s a || memT 1408 Lz s || memT 1408 Laz s || memT 1408 Lb s ||
      memT 1408 Lz₁ s

@[expose] def invClassesOK : Bool :=
  let a := tabW wordA
  let z := tabW wordZ
  let az := tabW wordAZ
  let b := tabW wordB
  let z₁ := tabW wordZ₁
  let Lz := classList invCap classz.rep
  let Laz := classList invCap classaz.rep
  let Lb := classList invCap classb.rep
  let Lz₁ := classList invCap classz₁.rep
  decide (classz.rep = wordZ ∧ classaz.rep = wordAZ ∧ classb.rep = wordB ∧ classz₁.rep = wordZ₁) &&
    wordOK wordA && wordOK wordAZ &&
    wclassOK invCap classz && wclassOK invCap classaz && wclassOK invCap classb &&
    wclassOK invCap classz₁ && enumW invCap 2048 sylow2Words &&
    !tblEq 1408 a z && !tblEq 1408 a az && !tblEq 1408 a b && !tblEq 1408 a z₁ &&
    !memT 1408 Lz az && !memT 1408 Lz b && !memT 1408 Lz z₁ && !memT 1408 Laz b &&
    !memT 1408 Laz z₁ && !memT 1408 Lb z₁ &&
    invCoverOK a Lz Laz Lb Lz₁ (subgroupList invCap sylow2Words)

end CFSG.EvenSporadicStandard.HNRecog
