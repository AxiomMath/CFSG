module

public import CFSG.LieType.Multipliers.O73DataInputs

public section

namespace CFSG.AGLEmbedding.R3.O73Three

open CFSG.LieType.Multipliers.O73

@[expose] def toMI (rows : List (List ℕ)) : Matrix Idx Idx (ZMod 3) :=
  Matrix.of fun a b => (((rows.getD (idx a) []).getD (idx b) 0 : ℕ) : ZMod 3)

@[expose] def rowsA : List (List ℕ) :=
  [[2, 1, 0, 2, 1, 1, 2], [0, 0, 1, 0, 1, 2, 1], [0, 1, 1, 1, 0, 2, 2], [1, 1, 1, 1, 2, 2, 2],
   [0, 1, 0, 1, 0, 0, 0], [0, 2, 2, 1, 0, 0, 0], [2, 0, 1, 0, 1, 1, 0]]

@[expose] def rowsB : List (List ℕ) :=
  [[1, 0, 2, 0, 1, 1, 1], [1, 1, 1, 2, 0, 1, 0], [1, 0, 2, 2, 0, 0, 1], [2, 2, 0, 1, 0, 1, 1],
   [2, 2, 2, 0, 2, 2, 2], [2, 0, 0, 1, 2, 2, 2], [0, 1, 2, 1, 0, 0, 1]]

@[expose] def matA : Matrix Idx Idx (ZMod 3) := toMI rowsA

@[expose] def matB : Matrix Idx Idx (ZMod 3) := toMI rowsB

@[expose] def tabA : Array ℕ := tabOf matA

@[expose] def tabB : Array ℕ := tabOf matB

@[expose] def rowsHA : List (List ℕ) :=
  [[2, 1, 2, 2, 0, 1, 0], [2, 1, 1, 0, 2, 1, 0], [0, 1, 2, 1, 1, 2, 1], [0, 2, 0, 0, 0, 2, 0],
   [1, 2, 1, 1, 2, 1, 0], [2, 1, 2, 0, 1, 1, 0], [1, 2, 1, 0, 2, 2, 2]]

@[expose] def rowsHAinv : List (List ℕ) :=
  [[0, 1, 0, 2, 0, 1, 0], [0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 1, 2, 1], [0, 1, 2, 2, 2, 0, 2],
   [2, 2, 1, 1, 1, 1, 1], [0, 1, 2, 2, 1, 2, 2], [0, 0, 0, 0, 0, 2, 2]]

@[expose] def rowsHB : List (List ℕ) :=
  [[1, 0, 1, 0, 2, 2, 2], [1, 1, 0, 2, 0, 1, 1], [0, 0, 0, 2, 1, 1, 0], [0, 1, 2, 1, 1, 2, 1],
   [2, 0, 2, 0, 2, 1, 1], [2, 0, 0, 1, 0, 0, 2], [2, 0, 2, 1, 1, 2, 2]]

@[expose] def rowsHBinv : List (List ℕ) :=
  [[1, 0, 1, 0, 2, 2, 2], [1, 2, 0, 2, 0, 1, 2], [2, 1, 0, 2, 1, 1, 1], [0, 2, 2, 1, 1, 0, 1],
   [1, 0, 0, 0, 1, 0, 0], [2, 2, 0, 1, 0, 0, 1], [2, 2, 1, 1, 2, 0, 2]]

@[expose] def matHA : Matrix Idx Idx (ZMod 3) := toMI rowsHA

@[expose] def matHAinv : Matrix Idx Idx (ZMod 3) := toMI rowsHAinv

@[expose] def matHB : Matrix Idx Idx (ZMod 3) := toMI rowsHB

@[expose] def matHBinv : Matrix Idx Idx (ZMod 3) := toMI rowsHBinv

@[expose] def rowsS2 : List (List ℕ) :=
  [[1, 2, 2, 0, 1, 0, 2], [0, 2, 1, 2, 0, 2, 1], [0, 0, 0, 2, 1, 1, 0], [0, 0, 0, 1, 0, 0, 0],
   [0, 1, 2, 0, 2, 2, 0], [0, 0, 1, 1, 0, 2, 1], [0, 1, 2, 1, 0, 0, 1]]

@[expose] def rowsS3 : List (List ℕ) :=
  [[1, 1, 2, 1, 1, 0, 2], [0, 0, 0, 2, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 0],
   [0, 1, 2, 2, 1, 1, 0], [0, 0, 0, 0, 2, 2, 0], [0, 0, 0, 1, 0, 0, 2]]

@[expose] def rowsS4 : List (List ℕ) :=
  [[1, 0, 1, 1, 2, 1, 1], [0, 1, 2, 2, 1, 2, 2], [0, 0, 1, 1, 2, 2, 1], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 1, 2, 1, 1], [0, 0, 2, 2, 1, 2, 0]]

@[expose] def rowsS5 : List (List ℕ) :=
  [[1, 0, 1, 2, 2, 1, 0], [0, 1, 1, 2, 2, 1, 0], [0, 0, 0, 1, 1, 2, 0], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]]

@[expose] def rowsS6 : List (List ℕ) :=
  [[1, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 1]]

@[expose] def rowsS7 : List (List ℕ) :=
  [[1, 0, 2, 2, 1, 0, 2], [0, 1, 1, 1, 1, 1, 2], [0, 0, 1, 0, 1, 2, 2], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 2, 1, 1, 2], [0, 0, 1, 1, 1, 1, 0]]

@[expose] def rowsS8 : List (List ℕ) :=
  [[1, 0, 0, 0, 1, 1, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def rowsS9 : List (List ℕ) :=
  [[1, 0, 0, 2, 0, 1, 1], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 1]]

@[expose] def rowsS10 : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 2, 2], [0, 0, 1, 0, 2, 2, 2], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1]]

@[expose] def rowsS11 : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 2, 1], [0, 0, 1, 0, 0, 2, 2], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 1]]

@[expose] def rowsS12 : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 2, 2], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 1]]

@[expose] def chainS : Array (Array ℕ) :=
  #[tabA, tabB, tabOf (toMI rowsS2), tabOf (toMI rowsS3), tabOf (toMI rowsS4), tabOf (toMI rowsS5),
   tabOf (toMI rowsS6), tabOf (toMI rowsS7), tabOf (toMI rowsS8), tabOf (toMI rowsS9),
   tabOf (toMI rowsS10), tabOf (toMI rowsS11), tabOf (toMI rowsS12)]

@[expose] def chainBase : List (Fin 2187) := [1, 3, 9, 27, 81, 243]

@[expose] def chainW : Array (List ℤ) :=
  #[[], [], [1, -2, -1, 2, 1, 2, 1, 2, 1], [-1, -2, -3, -2, 3, 1], [-4, -3, -4, -4, 3, 4],
   [-3, 5, 3], [-6, 4, 6, 4], [3, 5, -3], [-8, -5, 8, 7, 5], [-8, -9, -7, 8],
   [7, 10, -5, -6, -8, -6, 4, -3, 8, 4, 3], [-9, 7, 10, -8, -6, 11, 8], [-11, -12]]

end CFSG.AGLEmbedding.R3.O73Three
