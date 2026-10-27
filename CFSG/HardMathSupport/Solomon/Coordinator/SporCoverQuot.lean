module

public import CFSG.HardMathSupport.Solomon.Coordinator.SporCover
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicRankData
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.McL
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Suz
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi22
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.AGLEmbedding CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.HardMathSupport.Timmesfeld.SporadicRank

theorem sporCover_J3_pRank_quot_le
    (L : Type) [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have h4 := sporCover_J3_pRank_ge_four L hperf hZ he
  have hle : SporadicThreeRankLe .J3 3 :=
    sporadicThreeRankLe_of_carrier .J3 3 CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv (by
      intro _
      show CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.J3) ≤ 3
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.RankThree.Asc83Table.J3.native_J3.1])
  exact ((hle _ he).trans (by norm_num)).trans h4

theorem sporCover_McL_pRank_ge_five
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group)) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨D, hn, hA, hF⟩ := exists_spec_McL
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .McL ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group := b0
  obtain ⟨e⟩ := he
  have := succ_le_pRank_of_center_three hZ (e.trans b.symm) D hA hF
  omega

theorem sporCover_Suz_pRank_ge_six
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Suz).Group)) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨D, hn, hA, hF⟩ := exists_spec_Suz
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .Suz ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Suz).Group := b0
  obtain ⟨e⟩ := he
  have := succ_le_pRank_of_center_three hZ (e.trans b.symm) D hA hF
  omega

theorem sporCover_Fi22_pRank_ge_six
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group)) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨D, P, hn, hA, hF, -⟩ := sylowData_Fi22
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := b0
  obtain ⟨e⟩ := he
  have := succ_le_pRank_of_center_three hZ (e.trans b.symm) D hA hF
  omega

theorem sporCover_Fi24Prime_pRank_ge_eight
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi24Prime).Group)) :
    8 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨D, P, hn, hA, hF, -⟩ := sylowCover_Fi24
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .Fi24Prime ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi24Prime).Group := b0
  obtain ⟨e⟩ := he
  have := succ_le_pRank_of_center_three hZ (e.trans b.symm) D hA hF
  omega

end CFSG.HardMathSupport.Solomon.Coordinator
