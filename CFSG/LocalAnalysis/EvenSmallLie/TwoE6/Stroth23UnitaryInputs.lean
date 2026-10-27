module

public import CFSG.Monster.B.TwoA.Unitary.Twenty
public meta import CFSG.Monster.B.TwoA.Unitary.TwentyData
public meta import CFSG.Monster.B.TwoA.Unitary.TwentyAlg
public meta import CFSG.Monster.B.TwoA.Unitary.Form
import CFSG.Fischer.F4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Unitary CFSG.Fischer Matrix

attribute [local irreducible] decW u20RecRows u20Gens u20Words u20Basis

@[expose] def nuWord : List ℕ := [0, 3, 4, 7, 16]

@[expose] def rowsPow (R : Array ℕ) : ℕ → Array ℕ
  | 0 => idRows
  | n + 1 => rowsMul (rowsPow R n) R

@[expose] def rowsGeom (R : Array ℕ) : ℕ → Array ℕ
  | 0 => zeroRows
  | n + 1 => rowsXor (rowsGeom R n) (rowsPow R n)

@[expose] def nuMat : Matrix (Fin 6) (Fin 6) F4 := b6Mat 0 * b6Mat 3 * b6Mat 4 * b6Mat 7 * b6Mat 16

@[expose] def nuPowArr : Array (Array ℕ) :=
  #[#[1, 4, 16, 64, 256, 1024], #[73, 146, 195, 520, 1024, 2500],
    #[674, 833, 451, 2275, 2500, 3038], #[3011, 3649, 1475, 4042, 3038, 880],
    #[907, 3533, 3079, 2789, 880, 3722], #[3880, 688, 2009, 2006, 3722, 3309]]

@[expose] def nuPowM (i : ℕ) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun r => vec6 ((nuPowArr[i]!)[(r : ℕ)]!)

@[expose] def cycMat : Matrix (Fin 6) (Fin 6) F4 := Matrix.of fun i => nuPowM i 0

@[expose] def cycInv : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i => vec6 (#[1, 2276, 570, 3197, 3702, 975][(i : ℕ)]!)

@[expose] def IsScalarM (A : Matrix (Fin 6) (Fin 6) F4) : Prop :=
  ∀ p : Fin 6 × Fin 6, A p.1 p.2 = if p.1 = p.2 then A 0 0 else 0

instance (A : Matrix (Fin 6) (Fin 6) F4) : Decidable (IsScalarM A) :=
  inferInstanceAs (Decidable (∀ p : Fin 6 × Fin 6, A p.1 p.2 = if p.1 = p.2 then A 0 0 else 0))

end CFSG.EvenSmallLie.TwoE6
