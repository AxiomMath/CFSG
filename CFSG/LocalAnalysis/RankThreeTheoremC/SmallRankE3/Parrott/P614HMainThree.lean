module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614R3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HA5
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HB
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HOdd
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HConstr
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

namespace P614H

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H S K : Subgroup G} {x z : G}

theorem kbarL32_of_lieCase_three (k136 : KFact136Three) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) (hL : LieCase M H S K x z) : KbarL32 H K := by
  haveI := isSimpleGroup_kbar hyp h618
  have hidx : 2 ∣ (bar K (kRad H S K)).index := by
    rw [index_bar_kRad hyp h618]
    exact hL.rad_not_sylow
  rcases k136 (Kbar K) (isSimpleGroup_kbar hyp h618) (exists_ne_comm_kbar hyp h618) hL.chev
      (pRank_kbar h618) (bar K (kRad H S K)) (isPGroup_bar_kRad hyp)
      (bar_kRad_ne_bot hyp h618 hL) hidx (pCoreOf_normalizer_bar_kRad hyp h618 hL)
      (three_dvd_card_pElementSubgroup hyp h618 hL)
    with he | ⟨f, hf, -, -, hdvd, -⟩
  · obtain ⟨e⟩ := he
    refine ⟨e.toMonoidHom.comp (kbarMk K),
      e.surjective.comp (QuotientGroup.mk'_surjective _), fun k => ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      kbarMk_eq_one_iff hyp h618]
  · exfalso
    rw [pLayer_normalizer_bar_kRad_eq_bot hyp h618 hL, card_bot] at hdvd
    exact hf.one_lt.ne' (Nat.dvd_one.mp hdvd)

end P614H

open P614H

theorem piece620Three_holds : Piece620Three := by
  intro k136 kOut G _ _ P M x z H S K hyp h618 hcase
  have hkbar : (KbarA5 H K ∧ A5Case H S K) ∨ KbarL32 H K := by
    rcases hcase with hA | hL
    · exact Or.inl ⟨kbarA5_of_a5Case hyp h618 hA, hA⟩
    · exact Or.inr (kbarL32_of_lieCase_three k136 hyp h618 hL)
  have hcard : Nat.card (Kbar K) = 60 ∨ Nat.card (Kbar K) = 168 := by
    rcases hkbar with ⟨⟨f, hf, hk⟩, -⟩ | ⟨f, hf, hk⟩
    · left
      rw [card_kbar_eq hyp h618 f hf hk]
      exact card_alternatingGroup_five
    · right
      rw [card_kbar_eq hyp h618 f hf hk]
      exact L32Insp.card_GL
  obtain ⟨b, hbB, hbZ, hbK⟩ := exists_b kOut hyp h618 hcard
  exact ⟨b, hkbar, hbB, hbZ, hbK⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
