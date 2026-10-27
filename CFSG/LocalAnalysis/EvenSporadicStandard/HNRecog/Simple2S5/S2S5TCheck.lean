module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Letters

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HNRecog

@[expose] def tmuOne (k : Nat) : Bool :=
  let tg := tWords k
  let mg := mWords k
  let Tl := subgroupList 1000 tg
  let Ml := subgroupList 1000 mg
  let e := idT 1408
  let t₀ := tabW wordAZ
  let u := tabW (uWord k)
  let y₁ := tabW (yWord k 0)
  let y₂ := tabW (yWord k 1)
  wordOK wordAZ && wordOK (yWord k 0) && wordOK (yWord k 1) && wordOK (uWord k) &&
    enumW 1000 16 tg && enumW 1000 8 mg && memT 1408 Tl t₀ &&
    Tl.all (fun x => tblEq 1408 x e || tblEq 1408 x t₀ || !((tabsW tg).all (commTT 1408 x))) &&
    (tabsW mg).all (memT 1408 Tl) &&
    Ml.all (fun x => tblEq 1408 x e || tblEq 1408 x t₀ || !invoOK 1408 x) &&
    memT 1408 Tl u && !memT 1408 Ml u && involOK 1408 u && !tblEq 1408 u t₀ &&
    !commTT 1408 y₁ y₂

@[expose] def c8Check : Bool :=
  let Tl := subgroupList 1000 (tWords 0)
  let t₀ := tabW wordAZ
  let u := tabW (uWord 0)
  let t₀u := compT 1408 t₀ u
  Tl.all fun v => !involOK 1408 v || tblEq 1408 v t₀ ||
    Tl.any fun x => tblEq 1408 (compT 1408 x v) (compT 1408 u x) ||
      tblEq 1408 (compT 1408 x v) (compT 1408 t₀u x)

@[expose] def fixCheck : Bool :=
  let u := tabW (uWord 1)
  let t₀ := tabW wordAZ
  allIn 0 1408 (fun p => ap u p != p) && (List.range 1408).any fun p => ap t₀ p == p

@[expose] def tmuCheck : Bool := tmuOne 0 && tmuOne 1 && c8Check && fixCheck

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
