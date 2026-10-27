module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenJZero
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneDisc
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneBurnside
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenNine
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeXCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightTwoProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem AGL81CfgData.nineThreeList (h9 : AGL81NineCompetitorQ G) (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) : NineThreeListGroup p ↥K := by
  have hk := hd.kbar
  subst hk
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hne : d1KBar p M H ≠ ⊥ := fun h => hd.not_le_X0 (by rw [h]; exact bot_le)
  exact (h9 (aglGlobal_of_setting hS) p P M H (muAt_of_escape hesc) hd.maxH hd.not_le
    (exists_component_of_d1KBar_ne_bot hne) Q H hd.base hd.le_H hd.maxH hd.not_le hd.le_H
    (aglCovers_self H _)).1.list hne

theorem agl81ElevenElevenRankOneJZeroCfg_of (h9 : AGL81NineCompetitorQ G)
    (h9N : AGL81NineThreeNormalCfg G) (hKL : KFactNineThreeListRankOne)
    (hSA : KFactCaseTwoSylowAut) (hCT : KFactCaseTwoLocal)
    (hSU : KFactSUThreeTwoNoNormalThreePrime) (hKR : KFactL34ThreeRankTwo)
    (h7 : AGL81ElevenSevenCfg G) (h33 : AGL81ElevenThreeDvdCfg G)
    (hFA : AGL81ElevenNineFieldAut G) (h1011 : AGL81TenElevenOneDisc G)
    (h416 : AGL81FourSixteenAt G) (h1033 : AGL81TenThreeThreeCfg G)
    (hPC : AGL81ElevenElevenParabolicComm G) (h1014 : AGL81TenFourteenThreeCfgGen G)
    (hC : AGL81ElevenElevenRankOneCent G) : AGL81ElevenElevenRankOneJZeroCfg G := by
  intro hS p P M H Q K hσ hd hnc hK1 hH3 _hA6 L hL hLn hno
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  haveI : Fact p.Prime := ⟨hesc.prime⟩
  have hp : p.Prime := hesc.prime
  have hp2 : p ≠ 2 := hesc.ne_two
  have hXM : d1PlusCore p H K ≤ M := agl81NineThreeXCfg_of h9 hS p P M H Q K hd
  have hshape : IsCaseTwoGroup p ↥K := hKL p _ K (hd.nineThreeList h9 hS) hK1
  have hKn : K.Normal := h9N hS p P M H Q K hd
  obtain ⟨-, h72, h73, h74⟩ := h7 hS p P M H Q K hσ hd hnc L hL hLn hno
  have hJX : jZero H L ≤ d1PlusCore p H K := by
    rcases h73 with h | ⟨rfl, hL34⟩
    · exact h
    · exact absurd (hKR _ K hL34) (by omega)
  obtain ⟨W, y, z, hW⟩ := exists_rankOneSylowData hS hd hshape hKn hXM h72.le hH3 hSA hCT
  have hpJ : p ∣ Nat.card (jZero H L) := (h33 hS p P M H Q K hd hnc L hL hLn).trans
    (Subgroup.card_dvd_of_le (jOne_le_jZero H L))
  have hML : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hzJ := hW.z_mem_jZero hML hL.le hJX hpJ
  have hcyc : ∀ S : Subgroup G, S ≤ jZero H L → IsPGroup p S → IsCyclic S := fun S hSJ hSp =>
    RankOne.isCyclic_of_le_of_pRank_le_one hp2 (hSJ.trans hJX) hSp h72.le
  have hz2 : ¬ ∀ x ∈ jZero H L, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L) := fun hc =>
    RankOne.false_of_comm_jZero_of_cyclic hSU hp hp2 hzJ hW.z_order hcyc hpJ hc
  obtain ⟨a, haW, hap, hao, haJ⟩ := hW.elevenNine hS hd hshape hL hLn hJX hpJ hz2
    hFA agl81EightTwo_holds h1011 h416
  have hWJ : W ≤ Subgroup.normalizer (jZero H L : Set G) :=
    hW.le.trans ((RankOne.le_normalizer_inf hML).trans (le_normalizer_jZero H L))
  have hyQ : y ∈ d1LiftX p H Q K := hW.y_Q ▸ Subgroup.mem_zpowers y
  have hyC : y ∈ RankOne.centModTwo (jZero H L) :=
    RankOne.mem_centModTwo (hWJ hW.y_mem) (h74 hJX y hyQ)
  have haC : a ∈ RankOne.centModTwo (jZero H L) := RankOne.mem_centModTwo (hWJ haW) haJ
  have hAC : Subgroup.zpowers y ⊔ Subgroup.zpowers a ≤ RankOne.centModTwo (jZero H L) :=
    sup_le (Subgroup.zpowers_le.mpr hyC) (Subgroup.zpowers_le.mpr haC)
  have hAJ : ∀ b ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers a, ∀ x ∈ jZero H L,
      b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L) := fun b hb =>
    RankOne.comm_of_mem_centModTwo (hAC hb)
  have hAW : Subgroup.zpowers y ⊔ Subgroup.zpowers a ≤ W :=
    sup_le (Subgroup.zpowers_le.mpr hW.y_mem) (Subgroup.zpowers_le.mpr haW)
  have hlift : d1LiftX p H (Subgroup.zpowers y ⊔ Subgroup.zpowers a) K = d1LiftX p H Q K := by
    apply le_antisymm
    · calc d1LiftX p H (Subgroup.zpowers y ⊔ Subgroup.zpowers a) K ≤ d1LiftX p H W K :=
            Subgroup.map_mono (inf_le_inf_right _ fun x hx =>
              Subgroup.mem_subgroupOf.mpr (hAW (Subgroup.mem_subgroupOf.mp hx)))
        _ = d1LiftX p H Q K := by rw [hW.y_lift, hW.y_Q]
    · rw [hW.y_Q, Subgroup.zpowers_le]
      obtain ⟨y', ⟨-, hy'K⟩, hy'⟩ := hyQ
      refine ⟨y', ⟨?_, hy'K⟩, hy'⟩
      have hyA : (y' : G) ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers a := by
        rw [show (y' : G) = y from hy']
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
      exact hyA
  refine ⟨Subgroup.zpowers y ⊔ Subgroup.zpowers a, hAW.trans (hW.le.trans inf_le_left),
    hW.isAGLQ hS hd hnc hshape hKn hH3 hXM hL hLn hno hJX h72 hpJ hzJ hz2 haW hap hao hAJ h1033
      hPC h1014 hC,
    ?_, hAJ⟩
  obtain ⟨S, hS'⟩ := hd.sylowK_d1LiftX
  refine ⟨S, ?_⟩
  rw [hS', ← hlift, map_d1LiftX, inf_assoc, inf_idem]

end CFSG.LocalAnalysis.RankThreeTheoremC
