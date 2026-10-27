module

public import CFSG.LocalAnalysis.ComponentClassification.FooteTopExclusionMarkedSwap
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedComponentTools
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedInheritance

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteMarkedFactorCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (𝓢 : Set (Subgroup G)),
    FooteSwapSetting G t L 𝓢 →
    ∀ N H : Subgroup G, FooteMarked.Balanced 𝓢 (L ⧸ Open.fusionZStar L) N →
      FooteMarked.base N ≤ H → H ≠ ⊤ →
      ∀ K ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) N,
        ∃ J ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) H, K ⊔ oddCoreIn J = J

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem choiceNormalizer_of_covers {T : Type} [Group T] [IsSimpleGroup T] {𝓢 : Set (Subgroup G)}
    (hsimp : IsSimpleGroup G) (hFam : FooteMarked.IsomorphicFamily 𝓢 T) {N : Subgroup G}
    (hNc : FooteMarked.IsMarkedChoice 𝓢 T N)
    (hC : ∀ H : Subgroup G, FooteMarked.base N ≤ H → H ≠ ⊤ →
      ∀ K ∈ FooteMarked.markedComponents 𝓢 T N,
        ∃ J ∈ FooteMarked.markedComponents 𝓢 T H, K ⊔ oddCoreIn J = J)
    (hQ : ∀ K ∈ FooteMarked.markedComponents 𝓢 T N, CFSG.IsQuasisimple ↥K)
    (hO : ∀ K ∈ FooteMarked.markedComponents 𝓢 T N, ∀ b ∈ K, orderOf b = 2 →
      ∀ K' ∈ FooteMarked.markedComponents 𝓢 T N, K' ≠ K →
        IsTwoComponentIn K' (centralizer ({b} : Set G)))
    {𝒦 : Set (Subgroup G)} (h𝒦 : 𝒦 ⊆ FooteMarked.markedComponents 𝓢 T N) (hne : 𝒦.Nonempty) :
    normalizer ((sSup 𝒦 : Subgroup G) : Set G) ≠ ⊤ ∧
      FooteMarked.Balanced 𝓢 T (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) ∧
      FooteMarked.markedComponents 𝓢 T (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) =
        FooteMarked.markedComponents 𝓢 T N ∧
      normalizer ((sSup 𝒦 : Subgroup G) : Set G) ≤
        normalizer (FooteMarked.markedLayer 𝓢 T N : Set G) := by
  classical
  obtain ⟨A, hA𝒦⟩ := hne
  have hAN := h𝒦 hA𝒦
  have hH₀top : normalizer ((sSup 𝒦 : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    haveI := hsimp
    haveI : (sSup 𝒦 : Subgroup G).Normal := normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sSup 𝒦 : Subgroup G) with hbot | htop'
    · have hAbot : A = ⊥ := eq_bot_iff.mpr (hbot ▸ le_sSup hA𝒦)
      have := GSThmB.B5a.nontrivial_of_isPComponent_subgroupOf hAN.1.1 hAN.1.2
      rw [hAbot] at this
      exact not_nontrivial (⊥ : Subgroup G) this
    · refine FooteMarked.ne_top_of_balanced hsimp hNc.balanced (eq_top_iff.mpr ?_)
      rw [← htop']
      exact (sSup_le_sSup h𝒦).trans (FooteMarked.markedLayer_le 𝓢 T N)
  have hbase : FooteMarked.base N ≤ normalizer ((sSup 𝒦 : Subgroup G) : Set G) :=
    FooteMarked.le_normalizer_sSup fun K hK =>
      FooteMarked.base_le_normalizer_of_isTwoComponentIn (h𝒦 hK).1
  have hLift := hC _ hbase hH₀top
  have hbal := FooteMarked.balanced_of_oddCore_covers hFam hNc.balanced hbase hLift
  have hinside : ∀ B ∈ 𝒦, B ∈ FooteMarked.markedComponents 𝓢 T
      (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) := by
    intro B hB
    have hBN := h𝒦 hB
    have hDB : (sSup 𝒦 : Subgroup G) ≤ normalizer (B : Set G) := by
      refine sSup_le fun K hK => ?_
      by_cases hKB : K = B
      · rw [hKB]
        exact le_normalizer
      · exact (FooteMarked.le_centralizer_of_isTwoComponentIn hBN.1 (hQ B hBN) (h𝒦 hK).1
          (Ne.symm hKB)).trans (Subgroup.centralizer_le_normalizer (B : Set G))
    exact ⟨FooteMarked.isTwoComponentIn_of_le_normalizer (le_sSup hB) le_normalizer hDB le_rfl
      (hQ B hBN)
      (LocalCores.isQuasisimple_nontrivial (FooteMarked.Marked.quotient_quasisimple hFam hBN.2)),
      hBN.2⟩
  have hsub : FooteMarked.markedComponents 𝓢 T N ⊆ FooteMarked.markedComponents 𝓢 T
      (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) := by
    intro K hK
    by_cases hK𝒦 : K ∈ 𝒦
    · exact hinside K hK𝒦
    obtain ⟨J, hJ, hKJc⟩ := hLift K hK
    have hKJ : K ≤ J := le_sup_left.trans hKJc.le
    have hAH := hinside A hA𝒦
    have hAJ : A ≠ J := by
      intro hAJ
      have hAc : A ⊔ oddCoreIn J = J := by
        rw [← hAJ]
        exact sup_eq_left.mpr (map_subtype_le _)
      exact hK𝒦 (FooteMarked.eq_of_marked_oddCore_covers hbase hK hAN hJ hKJc hAc ▸ hA𝒦)
    obtain ⟨b, hbA, hb⟩ := FooteMarked.exists_involution_of_isTwoComponentIn hAN.1
    have hJb : J ≤ centralizer ({b} : Set G) := by
      intro y hy
      have hyA := FooteMarked.le_centralizer_of_isTwoComponentIn hAH.1 (hQ A hAN) hJ.1 hAJ hy
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hyA b hbA).symm
    have hJ' : IsTwoComponentIn J (normalizer ((sSup 𝒦 : Subgroup G) : Set G) ⊓
        centralizer ({b} : Set G)) :=
      Sol76.isTwoComponentIn_of_le hJ.1 (le_inf hJ.1.1 hJb) inf_le_left
    have hKb : IsTwoComponentIn K (centralizer ({b} : Set G)) :=
      hO A hAN b hbA hb K hK (fun h => hK𝒦 (h ▸ hA𝒦))
    have hK' : IsTwoComponentIn K (normalizer ((sSup 𝒦 : Subgroup G) : Set G) ⊓
        centralizer ({b} : Set G)) :=
      Sol76.isTwoComponentIn_of_le hKb (le_inf (hKJ.trans hJ.1.1) hKb.1) inf_le_right
    rw [Foote5.SolMax.eq_of_le_of_isTwoComponentIn hK' hJ' hKJ]
    exact hJ
  have hcomp : FooteMarked.markedComponents 𝓢 T (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) =
      FooteMarked.markedComponents 𝓢 T N :=
    (Set.eq_of_subset_of_ncard_le hsub (hNc.markedCount_le hbal) (Set.toFinite _)).symm
  refine ⟨hH₀top, hbal, hcomp, ?_⟩
  have h := FooteMarked.markedLayer_le_normalizer hFam
    (normalizer ((sSup 𝒦 : Subgroup G) : Set G))
  rwa [show FooteMarked.markedLayer 𝓢 T (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) =
    FooteMarked.markedLayer 𝓢 T N from congrArg sSup hcomp] at h

end Assembly

theorem footeMarkedChoiceNormalizer_of_factorCover (hF : FooteMarkedFactorCover)
    (hS : FooteMarkedChoiceSemisimple) : FooteMarkedChoiceNormalizer := by
  intro G _ _ t L 𝓢 hset N hNc 𝒦 h𝒦 hne
  haveI : IsSimpleGroup (L ⧸ Open.fusionZStar L) :=
    (GrSLit.fusionZStar_quotient_of_isPComponent hset.2.1.1.2.2.1.2.1
      hset.2.1.1.2.2.1.2.2).1
  obtain ⟨hQ, hO⟩ := hS G t L 𝓢 hset N hNc
  exact choiceNormalizer_of_covers hset.2.2.1 hset.2.2.2.2.1 hNc
    (fun H hH hHtop => hF G t L 𝓢 hset N H hNc.balanced hH hHtop) hQ hO h𝒦 hne

end CFSG.ComponentClassification.FooteLit
