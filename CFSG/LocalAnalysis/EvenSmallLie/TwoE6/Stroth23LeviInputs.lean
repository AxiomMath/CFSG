module

public import CFSG.Monster.B.Classical.UnitarySixForm
public import CFSG.Monster.B.Classical.UnitarySixBeta
public import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.Classical.UnitarySixForm
public meta import CFSG.Monster.B.Classical.UnitarySixBeta
public meta import CFSG.Monster.B.TwoA.Unitary.Form
import CFSG.Fischer.F4
public meta import Mathlib
public import Mathlib

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
open CFSG.Monster.B.Classical.UnitarySix

@[expose] def outA : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i => CFSG.Monster.B.TwoA.Unitary.vec6 (#[1025, 4, 16, 64, 256, 1024][(i : ℕ)]!)

@[expose] def outN : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i =>
    CFSG.Monster.B.TwoA.Unitary.vec6 (#[192, 2830, 3268, 3075, 2882, 2618][(i : ℕ)]!)

@[expose] def outNPow (k : ℕ) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i => CFSG.Monster.B.TwoA.Unitary.vec6
    ((#[#[2050, 3991, 1577, 1445, 1437, 1879], #[1450, 1728, 2916, 1179, 3173, 54],
      #[2233, 2298, 1831, 1962, 2660, 2787]][k]!)[(i : ℕ)]!)

end CFSG.EvenSmallLie.TwoE6
