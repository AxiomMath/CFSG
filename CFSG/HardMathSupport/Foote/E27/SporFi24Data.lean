module

public import CFSG.HardMathSupport.Foote.E27.OrbitF3

public section

namespace CFSG.HardMathSupport.Foote.E27.Fi24

open CFSG.Monster.B.Pinned CFSG.HardMathSupport.Foote.E27.OrbitF3

@[expose] def XRows : List (List ℕ) :=
  [[1, 1, 0, 1, 0, 1, 2, 2, 1, 0], [1, 0, 1, 1, 1, 1, 1, 0, 1, 2],
    [0, 0, 1, 2, 1, 2, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2, 1, 1, 2, 1],
    [1, 0, 0, 0, 0, 1, 2, 1, 1, 1], [2, 2, 0, 0, 1, 1, 0, 2, 2, 1],
    [0, 0, 1, 2, 1, 1, 2, 0, 1, 2], [0, 2, 1, 2, 2, 0, 2, 1, 1, 1],
    [1, 1, 0, 2, 1, 2, 2, 2, 1, 0], [0, 0, 1, 2, 1, 1, 1, 0, 0, 1]]

@[expose] def YRows : List (List ℕ) :=
  [[1, 2, 0, 0, 1, 0, 2, 1, 2, 0], [1, 0, 2, 0, 0, 1, 1, 0, 0, 0],
    [0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 1, 1],
    [0, 0, 1, 2, 2, 2, 1, 0, 2, 0], [0, 0, 2, 2, 0, 2, 2, 0, 1, 2],
    [0, 0, 1, 1, 2, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 2, 2, 2, 2],
    [0, 0, 1, 1, 1, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 0, 2, 2, 2, 0]]

@[expose] def base : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

@[expose] def XiRows : List (List ℕ) :=
  [[0, 1, 1, 1, 2, 1, 2, 1, 1, 0], [1, 2, 0, 1, 0, 2, 2, 0, 1, 1],
    [0, 0, 1, 2, 1, 0, 1, 2, 0, 1], [2, 2, 1, 0, 1, 1, 2, 0, 2, 1],
    [0, 2, 0, 1, 2, 2, 0, 2, 0, 1], [0, 2, 2, 2, 0, 0, 1, 1, 2, 1],
    [1, 1, 0, 1, 1, 0, 1, 1, 2, 2], [2, 2, 0, 2, 1, 2, 1, 0, 1, 1],
    [1, 2, 2, 2, 2, 1, 1, 2, 0, 0], [1, 0, 1, 0, 0, 2, 2, 0, 1, 0]]

@[expose] def YiRows : List (List ℕ) :=
  [[0, 1, 2, 0, 0, 1, 0, 2, 0, 1], [2, 1, 0, 0, 0, 0, 1, 0, 0, 2],
    [0, 0, 2, 2, 0, 1, 1, 0, 2, 2], [0, 0, 2, 0, 2, 1, 2, 0, 1, 1],
    [0, 0, 2, 0, 1, 1, 1, 2, 0, 1], [0, 0, 1, 0, 0, 1, 1, 1, 2, 1],
    [0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 2, 2],
    [0, 0, 2, 1, 2, 0, 0, 0, 2, 2], [0, 0, 1, 0, 0, 0, 2, 2, 0, 1]]

theorem X_mul_inv : rowsMat 3 10 XRows * rowsMat 3 10 XiRows = 1 := by decide +kernel
theorem X_inv_mul : rowsMat 3 10 XiRows * rowsMat 3 10 XRows = 1 := by decide +kernel
theorem Y_mul_inv : rowsMat 3 10 YRows * rowsMat 3 10 YiRows = 1 := by decide +kernel
theorem Y_inv_mul : rowsMat 3 10 YiRows * rowsMat 3 10 YRows = 1 := by decide +kernel

@[expose] def XU : GL (Fin 10) (ZMod 3) :=
  ⟨rowsMat 3 10 XRows, rowsMat 3 10 XiRows, X_mul_inv, X_inv_mul⟩

@[expose] def YU : GL (Fin 10) (ZMod 3) :=
  ⟨rowsMat 3 10 YRows, rowsMat 3 10 YiRows, Y_mul_inv, Y_inv_mul⟩

end CFSG.HardMathSupport.Foote.E27.Fi24
