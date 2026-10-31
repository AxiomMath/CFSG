module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLzMasks

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc24
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelOrbitBits
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLzMasks

@[expose] def d0Data : List ℕ :=
  [32, 63, 64, 95, 96, 127, 128, 159, 256, 287, 384, 415, 512, 543, 672, 703, 864, 895, 960, 991,
    1024, 1055, 1248, 1279, 1344, 1375, 1440, 1471, 1536, 1567, 1728, 1759, 1824, 1855, 2016,
    2047]

@[expose] def bitsOf (l : List ℕ) : ℕ := l.foldl (fun b m => b ||| 1 <<< m) 0

@[expose] def duadBits : ℕ := bitsOf o2Masks24

@[expose] def d0Bits : ℕ := bitsOf d0Data

@[expose] def pairOrb : ℕ := orbitBits [latX, latY] 2048 [32] (1 <<< 32)

abbrev pairProp : Prop :=
  (nodupB o2Masks24 (1 ||| 1 <<< 31) = true ∧ o2Masks24.length = 276 ∧
    ∀ m ∈ o2Masks24, m < 2048) ∧
  (nodupB d0Data 0 = true ∧ d0Data.length = 36) ∧
  (d0Data.all fun m => duadBits.testBit m && duadBits.testBit (m ^^^ 31)) = true ∧
  (o2Masks24.all fun m => !duadBits.testBit (m ^^^ 31) || d0Bits.testBit m) = true ∧
  (d0Data.all fun m => pairOrb.testBit m) = true

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
