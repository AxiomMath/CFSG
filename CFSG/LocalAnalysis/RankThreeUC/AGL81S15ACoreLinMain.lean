module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreCoverLin
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMatStmt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResStmt

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore CFSG.Open

theorem lieOddRankChevLinCore_of_matrix (hmat : LinCoreMatrix)
    (hG : CFSG.Open.GriessAllModelsStatement) : LieOddRankChevLinCore := by
  intro K _ _ hq l Q hv hQ he r hr hr2 hc
  obtain ⟨hrQ, hrl⟩ := hc
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨e⟩ := he
  have hl : 2 ≤ l := by
    by_contra h
    have hle : r ≤ l + 1 := Nat.le_of_dvd (by omega) hrl
    have := hr.two_le
    omega
  obtain ⟨F, instF, instFin, Z₀, hZ₀N, j, hcard, hZ₀D, hcenter, hrank⟩ :=
    coverIdLin hG hq hl hv hQ e
  haveI := hZ₀N
  rw [hrank r hr hr2]
  have hrF : r ∣ Fintype.card F - 1 := by
    rw [hcard]
    exact hrQ
  rw [hmat F (l + 1) r hr hr2 hrF hrl (by omega) Z₀ hZ₀D, hcenter]
  have hD : 0 < Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSL (l + 1) F)) :=
    Nat.card_pos
  have hZ : 0 < Nat.card Z₀ := Nat.card_pos
  have hdvd : Nat.card Z₀ ∣
      Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSL (l + 1) F)) :=
    Subgroup.card_dvd_of_le hZ₀D
  have hQ1 : 1 ≤ Q.card := by
    have := Fintype.one_lt_card (α := F)
    omega
  rw [rkLin_true_eq hr2 hQ1 hrQ hrl hZ hD hdvd, hcard]

end CFSG.LocalAnalysis.RankThreeUC.S15
