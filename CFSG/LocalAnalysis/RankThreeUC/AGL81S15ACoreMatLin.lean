module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMatStmt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreLinMat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonSylow
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreThree

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore CFSG.Open

theorem linCoreMatrix : LinCoreMatrix := by
  intro F _ _ m r hr hr2 hrF hrm hm3 Z₀ _ hZ₀
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hm4 : 4 ≤ m
  · rw [linMat_ge4 (perm_module_bound hr2 hm4) hr2 hm4 hrF
      (fun H hH => exists_conj_monomial_GL hr2 hrF (by omega) H hH) Z₀ hZ₀]
    congr 2
    apply propext
    tauto
  · have hm : m = 3 := by omega
    subst hm
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hrm
    subst hr3
    rw [pRank_statedSL_three hrF Z₀ hZ₀]
    simp [hm4]

end CFSG.LocalAnalysis.RankThreeUC.S15
