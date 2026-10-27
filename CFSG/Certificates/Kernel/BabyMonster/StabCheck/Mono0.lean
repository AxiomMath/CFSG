module

public import CFSG.Certificates.Kernel.BabyMonster.DyStabBlk
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data1
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data2
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.DyStabDefs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option maxRecDepth 100000

#bm_range CFSG.KC.BM.Dy.Stab ne0_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C0.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne1_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C1.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne2_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C2.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne3_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C3.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne4_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C4.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))
#bm_range CFSG.KC.BM.Dy.Stab ne5_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C5.rows (CFSG.KC.BM.dyElim 256 CFSG.KC.BM.Dyadic.Bs 0 CFSG.KC.BM.dyFail))

public section

namespace CFSG.KC.BM.Dy.Stab

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Dyadic CFSG.KC.BM.FixedLine

theorem neNeg : (rowsNeB C0.rows (CFSG.KC.BM.Lat.recOf C0.rows 70) 1).not = true := by quickRfl

theorem al0 : allAligned M0.b0 = true := by quickRfl
theorem v0 : netV M0.b0 (nthN G0.b0 0) = true := by quickRfl
theorem ne0t : rowsNeR C0.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al1 : allAligned M1.b0 = true := by quickRfl
theorem v1 : netV M1.b0 (nthN G1.b0 0) = true := by quickRfl
theorem ne1t : rowsNeR C1.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al2 : allAligned M2.b0 = true := by quickRfl
theorem v2 : netV M2.b0 (nthN G2.b0 0) = true := by quickRfl
theorem ne2t : rowsNeR C2.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al3 : allAligned M3.b0 = true := by quickRfl
theorem v3 : netV M3.b0 (nthN G3.b0 0) = true := by quickRfl
theorem ne3t : rowsNeR C3.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al4 : allAligned M4.b0 = true := by quickRfl
theorem v4 : netV M4.b0 (nthN G4.b0 0) = true := by quickRfl
theorem ne4t : rowsNeR C4.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

theorem al5 : allAligned M5.b0 = true := by quickRfl
theorem v5 : netV M5.b0 (nthN G5.b0 0) = true := by quickRfl
theorem ne5t : rowsNeR C5.rows (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) 4352 19 = true := by
  quickRfl

end CFSG.KC.BM.Dy.Stab

end
