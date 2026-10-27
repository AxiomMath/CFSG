module

public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOneAux
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem card_map_center_dvd_card_normalizer_inf {M S L : Subgroup G}
    {J : Subgroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))}
    (hJ : J = ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
      (barM M L)).map (QuotientGroup.mk' (Subgroup.center ↥(barM M L))))
    (hLM : L ≤ M) :
    Nat.card J ∣ Nat.card (Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) := by
  rw [hJ]
  refine (Subgroup.card_map_dvd _ _).trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (barM_mono inf_le_right)).toEquiv]
  exact CFSG.AGLEmbedding.card_barM_dvd (inf_le_right.trans hLM)

private theorem card_center_dvd_card_normalizer_inf {M S L : Subgroup G}
    (h93 : NineThreeTwo M S L) (hLM : L ≤ M) :
    Nat.card (Subgroup.center ↥(barM M L)) ∣
      Nat.card (Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) := by
  obtain ⟨-, T₀, hT₀, hNT₀⟩ := h93.2.1
  have hCnorm : Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (T₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.centralizer_le (show
      (T₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊆
        (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) from hT₀.1)).trans
      (Subgroup.centralizer_le_normalizer (T₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
  have hZle : (Subgroup.center ↥(barM M L)).map (barM M L).subtype ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
    rw [CFSG.center_map_subtype_eq_inf_centralizer]
    exact (inf_le_inf le_rfl hCnorm).trans hNT₀
  have hcard := (Subgroup.card_dvd_of_le hZle).trans
    (CFSG.AGLEmbedding.card_barM_dvd (inf_le_right.trans hLM))
  rwa [Subgroup.card_map_of_injective (barM M L).subtype_injective] at hcard


theorem pRank_barM_add_one_le_of_nineThreeTwo
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (h93 : NineThreeTwo M (pCoreOf 2 H) L)
    (h3L : CFSG.Open.pRank 3 (barM M L) ≤ 3) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hdL : ¬ d ∣ Nat.card (L ⊓ H : Subgroup G)) :
    CFSG.Open.pRank d (barM M L) + 1 ≤ max 2 (CFSG.Open.pRank 3 (barM M L)) ∧
      ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hphase : CFSG.AGLEmbedding.TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper
      (CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1)
  have h85 : CFSG.AGLEmbedding.Asc81bEightFive :=
    CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs
        (CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved))
  have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  have hS : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 H ⊓ L) L :=
    hphase.not_isSylowTwoOf_inf hK h85 hD2 hL
  obtain ⟨hcl, T, J, hT, hle, hne, htop, hJ⟩ :=
    CFSG.AGLEmbedding.BlockCyc.nineThreeTwo_parabolic hphase.asc81bHyp hL hS h93
  have hKsub_le : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ L ⊓ H := by
    refine le_inf inf_le_right ?_
    exact inf_le_left.trans (le_of_eq hphase.normalizer_twoCore_H)
  have hdKsub : ¬ d ∣ Nat.card (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L : Subgroup G) :=
    fun hdvd => hdL (hdvd.trans (Subgroup.card_dvd_of_le hKsub_le))
  have hJcard : Nat.card J ∣
      Nat.card (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L : Subgroup G) :=
    card_map_center_dvd_card_normalizer_inf hJ hL.le
  have hdJ : ¬ d ∣ Nat.card J := fun hdvd => hdKsub (hdvd.trans hJcard)
  have hZdiv : Nat.card (Subgroup.center ↥(barM M L)) ∣
      Nat.card (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L : Subgroup G) :=
    card_center_dvd_card_normalizer_inf h93 hL.le
  refine ⟨?_, fun hdvd => hdKsub (hdvd.trans hZdiv)⟩
  have h3top : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barM M L)]
    exact h3L
  have hmain := hN1 ↥(barM M L) hL.component.2.2 hcl T J hT hle hne htop d hd hd5 hdJ h3top
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := d) (barM M L),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barM M L)]
  exact hmain

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
