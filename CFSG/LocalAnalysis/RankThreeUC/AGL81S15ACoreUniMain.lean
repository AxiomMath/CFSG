module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreCoverUni
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMatStmt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResStmt

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore CFSG.Open

theorem lieOddRankChevUniCore_of_matrix (hmat : UniCoreMatrix)
    (hG : CFSG.Open.GriessAllModelsStatement) : LieOddRankChevUniCore := by
  intro K _ _ hq l Q hv hQ he r hr hr2 hc
  obtain ⟨hrQ, hrl⟩ := hc
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨e⟩ := he
  have hstd : 2 ≤ l ∧ (l = 2 → 3 ≤ Q.card) :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hl : 2 ≤ l := hstd.1
  have hq3 : l + 1 = 3 → 3 ≤ Q.card := fun h => hstd.2 (by omega)
  obtain ⟨F, instF, instFin, Z₀, hZ₀N, j, hcard, hZ₀D, hcenter, hrank⟩ :=
    coverIdUni hG hq hl hv hQ e
  haveI := hZ₀N
  rw [hrank r hr hr2]
  rw [hmat F Q.card (l + 1) r hr hr2 hcard hrQ hrl (by omega) hq3 Z₀ hZ₀D, hcenter]
  have hD : 0 < Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSU (l + 1) Q.card F)) :=
    Nat.card_pos
  have hZ : 0 < Nat.card Z₀ := Nat.card_pos
  have hdvd : Nat.card Z₀ ∣
      Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSU (l + 1) Q.card F)) :=
    Subgroup.card_dvd_of_le hZ₀D
  rw [rkLin_false_eq hr2 hrQ hrl hZ hD hdvd]

end CFSG.LocalAnalysis.RankThreeUC.S15
