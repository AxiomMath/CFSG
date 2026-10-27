module

public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankLie
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankOrth
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankAlt
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycMain
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2 (NoXBlockFor)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}


private theorem pRank_barM_add_one_le_of_isOrthogonalTwo
    {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hY : CFSG.AGLEmbedding.IsOrthogonalTwo ↥(barM M L))
    (h3 : CFSG.Open.pRank 3 (barM M L) ≤ 3) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    CFSG.Open.pRank d (barM M L) + 1 ≤ max 2 (CFSG.Open.pRank 3 (barM M L)) ∧
      ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  have h3' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ 3 := by
    rwa [← pRank_subgroup_eq_internal_top 3 (by norm_num) (barM M L)]
  obtain ⟨hle, hZ⟩ := pRank_le_one_of_isOrthogonalTwo hY h3' hd hd5
  refine ⟨?_, ?_⟩
  · rw [pRank_subgroup_eq_internal_top d hd.one_lt (barM M L)]
    calc CFSG.Open.pRank d (⊤ : Subgroup ↥(barM M L)) + 1 ≤ 1 + 1 :=
          Nat.add_le_add_right hle 1
      _ = 2 := rfl
      _ ≤ max 2 (CFSG.Open.pRank 3 (barM M L)) := le_max_left _ _
  · rw [hZ, Subgroup.card_bot]
    exact hd.not_dvd_one

private theorem pRank_barM_add_one_le_of_quot_center_alternating
    {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥(barM M L)) {n : ℕ} (hn : 5 ≤ n)
    (hA : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
      alternatingGroup (Fin n)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    CFSG.Open.pRank d (barM M L) + 1 ≤ max 2 (CFSG.Open.pRank 3 (barM M L)) ∧
      ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  have h := pRank_add_one_le_of_quot_center_alternating hq hn hA hd hd5
  rw [pRank_subgroup_eq_internal_top d hd.one_lt (barM M L),
    pRank_subgroup_eq_internal_top 3 (by norm_num) (barM M L)]
  exact h

private theorem pRank_barM_add_one_le_of_mulEquiv_alternating
    {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥(barM M L)) {n : ℕ}
    (e : ↥(barM M L) ≃* alternatingGroup (Fin n)) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    CFSG.Open.pRank d (barM M L) + 1 ≤ max 2 (CFSG.Open.pRank 3 (barM M L)) ∧
      ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  obtain ⟨hn, -, hA⟩ := quot_center_alternating_of_mulEquiv hq e
  exact pRank_barM_add_one_le_of_quot_center_alternating hq hn hA hd hd5

theorem pRank_barM_add_one_le_of_mem_weakBlockSet
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (h3L : CFSG.Open.pRank 3 (barM M L) ≤ 3) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hdL : ¬ d ∣ Nat.card (L ⊓ H : Subgroup G)) :
    CFSG.Open.pRank d (barM M L) + 1 ≤ max 2 (CFSG.Open.pRank 3 (barM M L)) ∧
      ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hphase : CFSG.AGLEmbedding.TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hMtop : M ≠ ⊤ := twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper hMtop
  have hBHS : CFSG.CGT.PushingUpLit.BHS.BHSLocalCStar :=
    CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have h85 : CFSG.AGLEmbedding.Asc81bEightFive :=
    CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs hBHS)
  have h93 : CFSG.AGLEmbedding.Asc81bNineThree :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.asc81bNineThree_holds
  have hD2 : NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  rcases hphase.nineThree hK h93 hL with h1' | h2' | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1' (hphase.nineThree_not_one hK h85 hD2 hL).1
  · exact pRank_barM_add_one_le_of_nineThreeTwo h1 h2 h25 hN1 h hL h2' h3L hd hd5 hdL
  · exact pRank_barM_add_one_le_of_isOrthogonalTwo h3.2.1 h3L hd hd5
  · exact pRank_barM_add_one_le_of_quot_center_alternating hL.component.2.2 (by norm_num)
      h4.2.2.1 hd hd5
  · obtain ⟨e⟩ := h5.2.1
    exact pRank_barM_add_one_le_of_mulEquiv_alternating hL.component.2.2 e hd hd5
  · obtain ⟨-, n, he, -⟩ := h6
    obtain ⟨e⟩ := he
    haveI : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
    haveI : Group.IsPerfect (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥(barM M L)))
        (QuotientGroup.mk'_surjective _)
    haveI : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      hL.component.2.2.2.toNontrivial
    have hn : 5 ≤ 2 * n :=
      CFSG.AGLEmbedding.BlockCyc.five_le_of_perfect_mulEquiv_alternatingGroup e
    exact pRank_barM_add_one_le_of_quot_center_alternating hL.component.2.2 hn ⟨e⟩ hd hd5
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    exact pRank_barM_add_one_le_of_mulEquiv_alternating hL.component.2.2 e hd hd5
  · obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
    exact pRank_barM_add_one_le_of_mulEquiv_alternating hL.component.2.2 e hd hd5

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
