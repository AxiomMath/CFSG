module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Reduce
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L616
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem prop614Sylow_of_ext (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (h : GL83SmallRankProp614Ext G) : GL83SmallRankProp614Sylow G := by
  intro P M hsit hsolv he x z hx hz H hH hBH _ ⟨S, hSHM, hS2, hSne, hBS⟩
  by_contra hHM
  obtain ⟨e⟩ := he
  obtain ⟨S', hSS', hS'max⟩ := exists_isMaxTwoInvariantIn_of_le
    (B := zpowers x ⊔ zpowers z) (X := H ⊓ M) (S := S) ⟨hSHM, hS2, hBS⟩
  obtain ⟨H₀, S₀, hext⟩ := exists_prop614Extremal (M := M) (B := zpowers x ⊔ zpowers z)
    ⟨H, S', ⟨hH, hBH, hHM, hS'max, ne_bot_of_le_ne_bot hSne hSS'⟩⟩
  have hmax := hext.isMax_self hS hU0 hD2 hsit hsolv e hx hz
  exact h P M hsit hsolv ⟨e⟩ x z hx hz H₀ S₀ hext
    (hext.pair.not_three_dvd_relIndex hS hU0 hD2 hsit hsolv e hx hz)
    hext.eq_normalizer_pCoreOf hmax (pCoreOf_le_of_isMaxTwoInvariantIn hext.pair.le hmax)
    (fun _ => hext.normalizer_le_of_pCoreOf_lt)
    (fun _ => hext.normalizer_le_of_characteristic hS hU0 hD2 hsit hsolv e hx hz)

theorem prop614_of_ext (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (h627 : GL83SmallRankProp627 G) (h632 : GL83SmallRankProp632 G)
    (h : GL83SmallRankProp614Ext G) : GL83SmallRankProp614 G :=
  prop614_of_sylow hS hU0 hD2 h627 h632 (prop614Sylow_of_ext hS hU0 hD2 h)

end CFSG.LocalAnalysis.RankThreeTheoremC
