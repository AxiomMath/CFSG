module

public import CFSG.Certificates.Kernel.BabyMonster.DyStabBlk
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data4
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data6
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.DyStabDefs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option maxRecDepth 100000

#bm_range CFSG.KC.BM.Dy.Stab ne13_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C13.rows 0)
#bm_range CFSG.KC.BM.Dy.Stab ne19_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C19.rows 0)
#bm_range CFSG.KC.BM.Dy.Stab ne21_ 0 68 (CFSG.KC.BM.Dy.rowsNeB CFSG.KC.BM.FixedLine.C21.rows 0)

public section

namespace CFSG.KC.BM.Dy.Stab

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Dyadic CFSG.KC.BM.FixedLine

theorem al13 : allAligned M13.b0 = true := by quickRfl
theorem v13 : netV M13.b0 (nthN G13.b0 0) = true := by quickRfl
theorem ne13t : rowsNeR C13.rows (nat_lit 0) 4352 19 = true := by
  quickRfl

theorem al19 : allAligned M19.b0 = true := by quickRfl
theorem v19 : netV M19.b0 (nthN G19.b0 0) = true := by quickRfl
theorem ne19t : rowsNeR C19.rows (nat_lit 0) 4352 19 = true := by
  quickRfl

theorem al21 : allAligned M21.b0 = true := by quickRfl
theorem v21 : netV M21.b0 (nthN G21.b0 0) = true := by quickRfl
theorem ne21t : rowsNeR C21.rows (nat_lit 0) 4352 19 = true := by
  quickRfl

end CFSG.KC.BM.Dy.Stab

end
