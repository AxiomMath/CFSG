module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.Chevalley.SimpleRootSubgroups
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice

@[expose] def fixed3 {n : ℕ} (C M : Matrix (Fin n) (Fin n) ℤ) : Finset (Fin n → ZMod 3) :=
  Finset.univ.filter fun z => ∀ j, ∑ k, z k * (((C * (M - 1)) k j : ℤ) : ZMod 3) = 0

@[expose] def e6SylWordX : List (Fin Tag.E6.rank) := [4, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]

@[expose] def e6SylWordY : List (Fin Tag.E6.rank) := [0, 2, 3, 4, 5, 4, 3, 2]

@[expose] def e6SylMX : List (List ℤ) := [[0, 0, 0, -1, 1, 0], [0, 1, 1, -2, 1, 0], [0, 1, 0, -2, 2, 0], [1, 2, 0, -3, 2, 0], [0, 2, 0, -2, 1, 0], [0, 1, 0, -1, 0, 1]]

@[expose] def e6SylMY : List (List ℤ) := [[0, 1, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, -1], [1, 1, -1, 1, 0, -1], [1, 1, -1, 0, 1, -1], [1, 1, -1, 0, 0, 0]]

@[expose] def e6SylWords : List (List Bool) :=
  [[],
   [false],
   [true],
   [false, false],
   [true, false],
   [false, true],
   [true, true],
   [true, false, false],
   [false, true, false],
   [true, true, false],
   [false, false, true],
   [true, false, true],
   [false, true, true],
   [false, true, false, false],
   [true, true, false, false],
   [false, false, true, false],
   [true, false, true, false],
   [false, true, true, false],
   [true, false, false, true],
   [false, true, false, true],
   [true, true, false, true],
   [false, false, true, true],
   [true, false, true, true],
   [false, false, true, false, false],
   [true, false, true, false, false],
   [false, true, true, false, false],
   [true, false, false, true, false],
   [false, true, false, true, false],
   [true, true, false, true, false],
   [false, false, true, true, false],
   [true, false, true, true, false],
   [true, true, false, false, true],
   [true, false, true, false, true],
   [false, true, true, false, true],
   [true, false, false, true, true],
   [false, true, false, true, true],
   [true, true, false, true, true],
   [true, false, false, true, false, false],
   [false, true, false, true, false, false],
   [true, true, false, true, false, false],
   [false, false, true, true, false, false],
   [true, false, true, true, false, false],
   [true, true, false, false, true, false],
   [true, false, true, false, true, false],
   [false, true, true, false, true, false],
   [true, false, false, true, true, false],
   [false, true, false, true, true, false],
   [true, true, false, true, true, false],
   [true, true, false, true, false, true],
   [true, false, true, true, false, true],
   [true, true, false, false, true, true],
   [true, false, true, false, true, true],
   [false, true, true, false, true, true],
   [true, true, false, false, true, false, false],
   [true, false, true, false, true, false, false],
   [false, true, true, false, true, false, false],
   [true, false, false, true, true, false, false],
   [false, true, false, true, true, false, false],
   [true, true, false, true, true, false, false],
   [true, true, false, true, false, true, false],
   [true, false, true, true, false, true, false],
   [true, true, false, false, true, true, false],
   [true, false, true, false, true, true, false],
   [false, true, true, false, true, true, false],
   [true, true, false, true, true, false, true],
   [true, true, false, true, false, true, true],
   [true, false, true, true, false, true, true],
   [true, true, false, true, false, true, false, false],
   [true, false, true, true, false, true, false, false],
   [true, true, false, false, true, true, false, false],
   [true, false, true, false, true, true, false, false],
   [false, true, true, false, true, true, false, false],
   [true, true, false, true, true, false, true, false],
   [true, true, false, true, false, true, true, false],
   [true, false, true, true, false, true, true, false],
   [true, true, false, true, true, false, true, true],
   [true, true, false, true, true, false, true, false, false],
   [true, true, false, true, false, true, true, false, false],
   [true, false, true, true, false, true, true, false, false],
   [true, true, false, true, true, false, true, true, false],
   [true, true, false, true, true, false, true, true, false, false]]

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
