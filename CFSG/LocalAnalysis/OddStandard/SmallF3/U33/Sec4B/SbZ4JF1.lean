module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B.ZJFin

theorem one_mem_M : one ∈ Mlist := by decide +kernel

theorem M_inv : ∀ m ∈ Mlist, ∀ n ∈ Plist, mmul m n = one → n ∈ Mlist := by decide +kernel

theorem M_fpf2 : ∀ m ∈ Mlist, mmul m R2 = mmul R2 m → m = one := by decide +kernel

theorem M_triv_V4 : ∀ m ∈ Mlist, ∀ n ∈ List.range 4, app m n = n := by decide +kernel

theorem L_not_M : L ∉ Mlist := by decide +kernel

theorem TL_not_M : mmul T L ∉ Mlist := by decide +kernel

theorem TL_distinct : one ≠ T ∧ one ≠ L ∧ one ≠ mmul T L ∧ T ≠ L ∧ T ≠ mmul T L ∧
    L ≠ mmul T L := by decide +kernel

theorem T_L_comm : mmul T L = mmul L T := by decide +kernel

end CFSG.OddStandard.SmallF3.HarrisU33.S4B.ZJFin
