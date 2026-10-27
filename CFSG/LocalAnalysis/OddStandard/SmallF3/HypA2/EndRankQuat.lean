module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndDataDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Phase2Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSetup

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem false_of_rank_two (hRk : RankTwoStd) {G : Type} [Group G] [Finite G] {x : G}
    {Y : Subgroup G} (hY : EndData G x Y)
    (h : 2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (Y : Set G))) : False := by
  haveI := hY.setting.simple
  rcases hRk G hY.setting.nonab hY.setting.kProper Y hY.standard h with
      ⟨n, hn, e⟩ | h | h | h | h | h
  · exact hY.setting.notCat (Or.inr (Or.inl ⟨n, by omega, e⟩))
  · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)
  · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)
  · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)
  · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)
  · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)

theorem false_of_quaternion (hQ : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    CFSG.OddStandard.StandardSetting G L → ∀ (S : Sylow 2 (Subgroup.centralizer (L : Set G))) (r :
    ℕ), 3 ≤ r → Nonempty (↥(S : Subgroup (Subgroup.centralizer (L : Set G))) ≃* QuaternionGroup (2 ^
    (r - 2))) → OddLieType G ∨ NativeSporadic.IsSporadic G
    .M12) {G : Type} [Group G] [Finite G] {x : G}
    {Y : Subgroup G} (hY : EndData G x Y) (S : Sylow 2 ↥(Subgroup.centralizer (Y : Set G)))
    {r : ℕ} (hr : 3 ≤ r)
    (e : Nonempty (↥(S : Subgroup ↥(Subgroup.centralizer (Y : Set G))) ≃*
      QuaternionGroup (2 ^ (r - 2)))) : False := by
  haveI := hY.setting.simple
  have hstd : CFSG.OddStandard.StandardSetting G Y :=
    ⟨hY.setting.simple, hY.setting.nonab, hY.setting.kProper, hY.standard⟩
  rcases hQ G Y hstd S r hr e with h | h
  · exact hY.setting.notCat
      (CFSG.ComponentClassification.HarrisLit.catalog_of_oddLieType h)
  · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)

end CFSG.OddStandard.SmallF3.HypA2
