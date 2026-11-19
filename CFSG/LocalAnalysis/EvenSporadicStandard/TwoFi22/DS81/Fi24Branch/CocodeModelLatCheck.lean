module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLzMasks

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc24
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelOrbitBits
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLzMasks

@[expose] def latRoots : List ℕ := [0, 31, 32, 160, 1, 7, 34]

@[expose] def latSizes : List ℕ := [1, 1, 36, 90, 240, 240, 1440]

@[expose] def latOrb (i : ℕ) : ℕ :=
  orbitBits [latX, latY] 2048 [latRoots.getD i 0] (1 <<< latRoots.getD i 0)

abbrev latticeOrbitsProp : Prop :=
  (∀ n < 2048, ((List.range 7).filter fun i => (latOrb i).testBit n).length = 1) ∧
  (∀ i < 7, ((List.range 2048).filter fun n => (latOrb i).testBit n).length = latSizes.getD i 0) ∧
  (∀ m ∈ w0Basis, ∃ i < 4, (latOrb i).testBit m = true)

@[expose] def r0Word : List ℕ := [0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1]

@[expose] def r0Arr : Array ℕ := wArr [lzXArr, lzYArr] r0Word

@[expose] def wActM : List ℕ → ℕ → ℕ
  | [], c => c
  | g :: w, c => actM (if g = 0 then mxCols else myCols) (wActM w c)

abbrev r0Prop : Prop :=
  (cArr r0Arr (cArr r0Arr r0Arr) = idArr ∧ ∃ i < 24, r0Arr[i]! ≠ i) ∧
  (∀ i < 24, r0Arr[i]! / 4 = i / 4) ∧
  (∀ c < 64, ∃ i < 24, (ksC c)[i]! ≠ r0Arr[i]!) ∧
  (∀ c < 64, c ≠ 0 → wActM r0Word c ≠ c) ∧
  (∀ j < 11, act11 r0Arr (2 ^ j) ^^^ 2 ^ j ∈ combos w0Basis)

abbrev latticeProp : Prop := latticeOrbitsProp ∧ r0Prop

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
