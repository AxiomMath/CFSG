module

public import CFSG.Certificates.Kernel.BabyMonster.DyStabBlk
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data3
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data4
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.DyStabDefs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option maxRecDepth 100000

#bm_range CFSG.KC.BM.Dy.Stab ne6_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C6.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne7_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C7.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne8_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C8.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne9_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C9.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne10_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C10.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne12_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C12.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))

public section

namespace CFSG.KC.BM.Dy.Stab

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Dyadic CFSG.KC.BM.FixedLine

theorem al6 : allAligned M6.b0 = true := by quickRfl
theorem v6 : netV M6.b0 (nthN G6.b0 0) = true := by quickRfl
theorem ne6t : rowsNeR C6.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al7 : allAligned M7.b0 = true := by quickRfl
theorem v7 : netV M7.b0 (nthN G7.b0 0) = true := by quickRfl
theorem ne7t : rowsNeR C7.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al8 : allAligned M8.b0 = true := by quickRfl
theorem v8 : netV M8.b0 (nthN G8.b0 0) = true := by quickRfl
theorem ne8t : rowsNeR C8.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al9 : allAligned M9.b0 = true := by quickRfl
theorem v9 : netV M9.b0 (nthN G9.b0 0) = true := by quickRfl
theorem ne9t : rowsNeR C9.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al10 : allAligned M10.b0 = true := by quickRfl
theorem v10 : netV M10.b0 (nthN G10.b0 0) = true := by quickRfl
theorem ne10t : rowsNeR C10.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al12 : allAligned M12.b0 = true := by quickRfl
theorem v12 : netV M12.b0 (nthN G12.b0 0) = true := by quickRfl
theorem ne12t : rowsNeR C12.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

end CFSG.KC.BM.Dy.Stab

end
