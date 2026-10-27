module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6TwoData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6R6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Malle.E27Lie.ExcCross
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross (laE6 lbE6)

#kc_repo #kc_decls CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6R6 "CFSG/HardMathSupport/Malle/E27Lie/ExcCross/data/e6two_r6.txt" 520 8876343044976030916

@[expose] def m4 (L : List ℕ) (o : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => ((L.getD (o + 4 * i.val + j.val) 0 : ℕ) : ℤ) - 8

@[expose] noncomputable def mXAB : Matrix (Fin 4) (Fin 4) ℤ := m4 dXAB 0

@[expose] noncomputable def mXAB2 : Matrix (Fin 4) (Fin 4) ℤ := m4 dXAB2 0

@[expose] noncomputable def zsAB (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ := m4 dZsAB (16 * k.val)

@[expose] noncomputable def zsAB2 (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ := m4 dZsAB2 (16 * k.val)

theorem r6_XAB : R6 e6XAB = mXAB := by decide +kernel

theorem r6_XAB2 : R6 e6XAB2 = mXAB2 := by decide +kernel

theorem r6_la : R6 laE6 = zsAB 0 := by decide +kernel

theorem r6_L2AB : R6 ([2, 3, 4, 3] : List (Fin Tag.E6.rank)) = zsAB 1 := by decide +kernel

theorem r6_zsAB_2 :
    R6 (laE6 ++ ([2, 3, 4, 3] : List (Fin Tag.E6.rank)) ++ laE6 ++ laE6) = zsAB 2 := by
  decide +kernel

theorem r6_zsAB_3 :
    R6 (laE6 ++ laE6 ++ ([2, 3, 4, 3] : List (Fin Tag.E6.rank)) ++ laE6) = zsAB 3 := by
  decide +kernel

theorem r6_la2 : R6 laE6 = zsAB2 0 := by decide +kernel

theorem r6_L2AB2 : R6 ([2, 3, 2, 4] : List (Fin Tag.E6.rank)) = zsAB2 1 := by decide +kernel

theorem r6_zsAB2_2 :
    R6 (laE6 ++ ([2, 3, 2, 4] : List (Fin Tag.E6.rank)) ++ laE6 ++ laE6) = zsAB2 2 := by
  decide +kernel

theorem r6_zsAB2_3 :
    R6 (laE6 ++ laE6 ++ ([2, 3, 2, 4] : List (Fin Tag.E6.rank)) ++ laE6) = zsAB2 3 := by
  decide +kernel

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6R6

end
