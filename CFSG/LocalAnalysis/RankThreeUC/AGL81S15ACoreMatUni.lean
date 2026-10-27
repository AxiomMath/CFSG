module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMatStmt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreUniMat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonSylow
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreThree

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore CFSG.Open

theorem uniCoreMatrix : UniCoreMatrix := by
  intro F _ _ q m r hr hr2 hF hrq hrm hm3 hq3 Z₀ _ hZ₀
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hm4 : 4 ≤ m
  · rw [uniMat_ge4 (perm_module_bound hr2 hm4) hr2 hm4 hF hrq
      (fun H hHU hH => exists_conj_monomial_GU hr2 hF hrq (by omega) H
        (hHU.trans
          CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU)
        hH) Z₀ hZ₀]
    congr 2
    apply propext
    tauto
  · have hm : m = 3 := by omega
    subst hm
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hrm
    subst hr3
    rw [pRank_statedSU_three hF (hq3 rfl) hrq Z₀ hZ₀]
    simp [hm4]

end CFSG.LocalAnalysis.RankThreeUC.S15
