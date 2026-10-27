module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.WeylE6Data

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

@[expose] def e6SylList (w : List Bool) : List (List ℤ) :=
  w.foldr (fun b acc => lmul Tag.E6.rank (if b then e6SylMY else e6SylMX) acc) (lid Tag.E6.rank)

@[expose] def e6SylS : List (Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) :=
  e6SylWords.map fun w => toMat Tag.E6.rank (e6SylList w)

set_option maxRecDepth 100000 in
theorem e6S_fixed3 :
    ∀ M ∈ e6SylS, M * M * M = 1 → 81 ≤ (fixed3 Tag.E6.cartan M).card := by
  decide +kernel


end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
