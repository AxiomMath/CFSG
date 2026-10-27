module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactWiring3Kf1
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridgeAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSetup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem gnSetting_of_subgroup (hK : CFSG.Open.IsKProper G) {M T : Subgroup G} (hMtop : M ≠ ⊤)
    (hc : CharTwo M) (hT : IsSylowTwoOf T M)
    (hX : ∀ Y : Subgroup G, Y ≤ M → IsSubnormal Y M → InClassXBlock Y → False) :
    GNSetting ↥M (T.subgroupOf M) where
  kGroup := CFSG.LocalAnalysis.RankThreeTheoremC.isKGroup_of_ne_top_of_isKProper hK hMtop
  sylow := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    · show ¬ 2 ∣ (T.subgroupOf M).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hT.2.2
  charTwo := charTwo_top_of_le hc (pCoreOf_le 2 M) le_rfl
  noXBlock := by
    intro Y hYsub hY
    set Y' : Subgroup G := Y.map M.subtype with hY'
    have hs : IsSubnormal Y' M := by
      have h := cfsg_isSubnormal_map M.subtype hYsub
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    have hY'M : Y' ≤ M := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hXY : CFSG.RankThree.PartOne.InClassX ↥Y :=
      CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hY
    have hXY' : CFSG.RankThree.PartOne.InClassX ↥Y' :=
      CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv (Y.equivMapOfInjective M.subtype
        M.subtype_injective) hXY
    exact hX Y' hY'M hs (CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hXY')

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
