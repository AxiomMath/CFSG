module

public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBlockTransferHyp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Only
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem isSubnormal_map_subtype {G : Type} [Group G] {M : Subgroup G} {H K : Subgroup ↥M}
    (h : IsSubnormal H K) : IsSubnormal (H.map M.subtype) (K.map M.subtype) :=
  h.map M.subtype

theorem gnSetting_of_maxTwoLocal {G : Type} [Group G] [Finite G] (hglob : AGLGlobal G)
    (hX : D1NoXBlock) {M T : Subgroup G} (hM : GLBIsMaxTwoLocal M) (hT : IsSylowTwoOf T M) :
    GNSetting ↥M (T.subgroupOf M) := by
  haveI := hglob.simple
  have hMtop : M ≠ ⊤ := twoLocal_ne_top hglob.nonab hM.1
  refine ⟨CFSG.AGLEmbeddingD2.McLaughlin.cfsgIsKGroup_of_open
    (CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hglob.kProper hMtop), ?_,
    CFSG.QuasithinUnique.Setup.Lift.charTwo_top (hglob.charTwo M hM.1), ?_⟩
  · refine ⟨le_top, hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm, ?_⟩
    have : ((T.subgroupOf M).subgroupOf (⊤ : Subgroup ↥M)).index = (T.subgroupOf M).index :=
      Subgroup.relIndex_top_right _
    rw [this]
    exact hT.2.2
  · intro Y hsn hY
    refine hX G hglob M (Y.map M.subtype) hM (Subgroup.map_subtype_le Y) ?_ ?_
    · have := isSubnormal_map_subtype hsn
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    · exact CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX
        (CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv
          (Y.equivMapOfInjective M.subtype M.subtype_injective)
          (CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hY))

theorem D2L34BetaConf.gnSetting {d : TauCeti.ValidLieTypeIndex} {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf d P M A H R Rbar K)
    (hX : D1NoXBlock) {T : Subgroup G} (hT : IsSylowTwoOf T M) :
    GNSetting ↥M (T.subgroupOf M) :=
  gnSetting_of_maxTwoLocal hc.glob.toAGLGlobal hX hc.esc.maxTwoLocal_M hT

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
