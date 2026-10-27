module

public import CFSG.LocalAnalysis.ComponentClassification.FooteTopExclusionGSFamily
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedConjugacy
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedTransport
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedChoiceTools

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteSwapSetting (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G)
    (𝓢 : Set (Subgroup G)) : Prop :=
  FooteMinimal G ∧ FooteCounterexample G t L ∧ IsSimpleGroup G ∧
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) ∧
    FooteMarked.IsomorphicFamily 𝓢 (L ⧸ Open.fusionZStar L) ∧
    ∃ (z s : G) (Y : Subgroup G), orderOf z = 2 ∧ orderOf s = 2 ∧ z * s = s * z ∧
      IsTwoComponentIn Y (centralizer ({z} : Set G)) ∧ Y ∈ 𝓢 ∧ conjugate Y s ≠ Y

@[expose] def FooteMarkedAbsorption : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (𝓢 : Set (Subgroup G)),
    FooteSwapSetting G t L 𝓢 →
    ∀ H M : Subgroup G, H ≠ ⊤ → FooteMarked.Balanced 𝓢 (L ⧸ Open.fusionZStar L) H →
      FooteMarked.Marked 𝓢 (L ⧸ Open.fusionZStar L) M → M ≤ H →
      (∃ a ∈ H, orderOf a = 2 ∧ a ∈ UnbalancedLayer.coreActionKernel M) →
      ∃ K ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) H, M ≤ K

@[expose] def FooteMarkedEmbeddingExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (𝓢 : Set (Subgroup G)),
    FooteSwapSetting G t L 𝓢 →
    ∀ M : Subgroup G, M ≠ ⊤ → FooteMarked.Balanced 𝓢 (L ⧸ Open.fusionZStar L) M →
      normalizer (FooteMarked.markedLayer 𝓢 (L ⧸ Open.fusionZStar L) M : Set G) = M →
      (∀ K ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) M, ∀ x ∈ K,
        orderOf x = 2 → centralizer ({x} : Set G) ≤ M) → False

@[expose] def FooteMarkedChoiceSemisimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (𝓢 : Set (Subgroup G)),
    FooteSwapSetting G t L 𝓢 →
    ∀ N : Subgroup G, FooteMarked.IsMarkedChoice 𝓢 (L ⧸ Open.fusionZStar L) N →
      (∀ K ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) N,
        CFSG.IsQuasisimple ↥K) ∧
      ∀ K ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) N, ∀ b ∈ K,
        orderOf b = 2 → ∀ K' ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) N,
          K' ≠ K → IsTwoComponentIn K' (centralizer ({b} : Set G))

@[expose] def FooteMarkedChoiceNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (𝓢 : Set (Subgroup G)),
    FooteSwapSetting G t L 𝓢 →
    ∀ N : Subgroup G, FooteMarked.IsMarkedChoice 𝓢 (L ⧸ Open.fusionZStar L) N →
    ∀ 𝒦 : Set (Subgroup G), 𝒦 ⊆ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) N →
      𝒦.Nonempty →
      normalizer ((sSup 𝒦 : Subgroup G) : Set G) ≠ ⊤ ∧
        FooteMarked.Balanced 𝓢 (L ⧸ Open.fusionZStar L)
          (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) ∧
        FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L)
            (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) =
          FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) N ∧
        normalizer ((sSup 𝒦 : Subgroup G) : Set G) ≤
          normalizer (FooteMarked.markedLayer 𝓢 (L ⧸ Open.fusionZStar L) N : Set G)

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem marked_of_mem_of_isTwoComponentIn {T : Type} [Group T] {𝓢 : Set (Subgroup G)}
    (hFam : FooteMarked.IsomorphicFamily 𝓢 T) {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : IsTwoComponentIn J (centralizer ({a} : Set G))) (hJ : J ∈ 𝓢) :
    FooteMarked.Marked 𝓢 T J := by
  have hJperf : Group.IsPerfect J := GSThmB.B5a.isPerfect_of_isPComponent_subgroupOf hJa.1 hJa.2
  have haC : a ∈ centralizer (J : Set G) :=
    mem_centralizer_iff.mpr fun j hj => mem_centralizer_singleton_iff.mp (hJa.1 hj)
  have hfix : FooteMarked.fixedShadowAt J a = J := by
    apply le_antisymm (FooteMarked.fixedShadowAt_le J a)
    rw [← FooteMarked.fixedShadow_zpowers]
    exact FooteMarked.le_fixedShadow_of_perfect hJperf
      (le_inf le_rfl (by rw [UnbalancedLayer.centralizer_zpowers_eq]; exact hJa.1))
  exact ⟨hJperf, hFam.2.1 J hJ, a, ha, GSThmB.B5a.centralizer_le_coreActionKernel J haC, J, hJ,
    by rw [hfix]⟩

theorem balanced_centralizer_of_swap {T : Type} [Group T] {𝓢 : Set (Subgroup G)}
    (hFam : FooteMarked.IsomorphicFamily 𝓢 T) {z s : G} {Y : Subgroup G} (hz : orderOf z = 2)
    (hzs : z * s = s * z) (hYz : IsTwoComponentIn Y (centralizer ({z} : Set G))) (hY : Y ∈ 𝓢)
    (hYs : conjugate Y s ≠ Y) : FooteMarked.Balanced 𝓢 T (centralizer ({z} : Set G)) := by
  classical
  have hsC : s ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr hzs.symm
  have hYsz : IsTwoComponentIn (conjugate Y s) (centralizer ({z} : Set G)) :=
    ⟨FooteMarked.conjugate_le_of_mem hYz.1 hsC,
      FooteMarked.isPComponent_conjugate_subgroupOf hsC hYz.2⟩
  have hsub : ({Y, conjugate Y s} : Set (Subgroup G)) ⊆
      FooteMarked.markedComponents 𝓢 T (centralizer ({z} : Set G)) := by
    intro K hK
    rcases hK with rfl | hK
    · exact ⟨hYz, marked_of_mem_of_isTwoComponentIn hFam hz hYz hY⟩
    · rw [Set.mem_singleton_iff] at hK
      subst hK
      exact ⟨hYsz, marked_of_mem_of_isTwoComponentIn hFam hz hYsz (hFam.2.2.1 Y hY s)⟩
  have hcount : 2 ≤ FooteMarked.markedCount 𝓢 T (centralizer ({z} : Set G)) :=
    calc 2 = ({Y, conjugate Y s} : Set (Subgroup G)).ncard := (Set.ncard_pair hYs.symm).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hzK : z ∈ FooteMarked.baseKernel 𝓢 T (centralizer ({z} : Set G)) :=
    ⟨mem_sup_left (mem_oddTwoCoreIn_of_central (mem_centralizer_singleton_iff.mpr rfl)
        (fun n hn => mem_centralizer_singleton_iff.mp hn) hz),
      GSLit.mem_coreActionKernel_of_le_centralizer (FooteMarked.markedLayer_le 𝓢 T _)⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hzK
  rw [hz] at hdvd
  exact ⟨hcount, Or.inr (even_iff_two_dvd.mpr hdvd)⟩

theorem false_of_isMarkedChoice {T : Type} [Group T] {𝓢 : Set (Subgroup G)}
    (hFam : FooteMarked.IsomorphicFamily 𝓢 T) {N : Subgroup G}
    (hNc : FooteMarked.IsMarkedChoice 𝓢 T N)
    (hA : ∀ H M : Subgroup G, H ≠ ⊤ → FooteMarked.Balanced 𝓢 T H → FooteMarked.Marked 𝓢 T M →
      M ≤ H → (∃ a ∈ H, orderOf a = 2 ∧ a ∈ UnbalancedLayer.coreActionKernel M) →
      ∃ K ∈ FooteMarked.markedComponents 𝓢 T H, M ≤ K)
    (hE : ∀ M : Subgroup G, M ≠ ⊤ → FooteMarked.Balanced 𝓢 T M →
      normalizer (FooteMarked.markedLayer 𝓢 T M : Set G) = M →
      (∀ K ∈ FooteMarked.markedComponents 𝓢 T M, ∀ x ∈ K, orderOf x = 2 →
        centralizer ({x} : Set G) ≤ M) → False)
    (hQ : ∀ K ∈ FooteMarked.markedComponents 𝓢 T N, CFSG.IsQuasisimple ↥K)
    (hO : ∀ K ∈ FooteMarked.markedComponents 𝓢 T N, ∀ b ∈ K, orderOf b = 2 →
      ∀ K' ∈ FooteMarked.markedComponents 𝓢 T N, K' ≠ K →
        IsTwoComponentIn K' (centralizer ({b} : Set G)))
    (hN : ∀ 𝒦 : Set (Subgroup G), 𝒦 ⊆ FooteMarked.markedComponents 𝓢 T N → 𝒦.Nonempty →
      normalizer ((sSup 𝒦 : Subgroup G) : Set G) ≠ ⊤ ∧
        FooteMarked.Balanced 𝓢 T (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) ∧
        FooteMarked.markedComponents 𝓢 T (normalizer ((sSup 𝒦 : Subgroup G) : Set G)) =
          FooteMarked.markedComponents 𝓢 T N ∧
        normalizer ((sSup 𝒦 : Subgroup G) : Set G) ≤
          normalizer (FooteMarked.markedLayer 𝓢 T N : Set G)) :
    False := by
  classical
  have h2 : 1 < (FooteMarked.markedComponents 𝓢 T N).ncard := hNc.balanced.1
  have hne : (FooteMarked.markedComponents 𝓢 T N).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  have hHtop : normalizer (FooteMarked.markedLayer 𝓢 T N : Set G) ≠ ⊤ :=
    (hN _ subset_rfl hne).1
  have hHbal : FooteMarked.Balanced 𝓢 T (normalizer (FooteMarked.markedLayer 𝓢 T N : Set G)) :=
    (hN _ subset_rfl hne).2.1
  have hHcomp : FooteMarked.markedComponents 𝓢 T
      (normalizer (FooteMarked.markedLayer 𝓢 T N : Set G)) =
        FooteMarked.markedComponents 𝓢 T N :=
    (hN _ subset_rfl hne).2.2.1
  have hcent : ∀ K ∈ FooteMarked.markedComponents 𝓢 T N, ∀ x ∈ K, orderOf x = 2 →
      centralizer ({x} : Set G) ≤ normalizer (FooteMarked.markedLayer 𝓢 T N : Set G) := by
    intro K hK x hxK hx
    obtain ⟨K', hK', hK'K⟩ := Set.exists_ne_of_one_lt_ncard h2 K
    have hK'x : IsTwoComponentIn K' (centralizer ({x} : Set G)) := hO K hK x hxK hx K' hK' hK'K
    have hK'H : normalizer (K' : Set G) ≤ normalizer (FooteMarked.markedLayer 𝓢 T N : Set G) := by
      have h := (hN {K'} (Set.singleton_subset_iff.mpr hK') (Set.singleton_nonempty K')).2.2.2
      rwa [sSup_singleton] at h
    have hLx : twoLayerIn (centralizer ({x} : Set G)) ≤
        normalizer (FooteMarked.markedLayer 𝓢 T N : Set G) :=
      (twoLayerIn_le_normalizer hK'x.1 hK'x.2).trans hK'H
    have hKD : K ≤ FooteMarked.markedLayer 𝓢 T N := le_sSup hK
    have hxH : x ∈ normalizer (FooteMarked.markedLayer 𝓢 T N : Set G) :=
      Subgroup.le_normalizer (hKD hxK)
    have hsub : FooteMarked.markedComponents 𝓢 T (centralizer ({x} : Set G)) ⊆
        FooteMarked.markedComponents 𝓢 T N := by
      intro M hM
      have hMH : M ≤ normalizer (FooteMarked.markedLayer 𝓢 T N : Set G) :=
        (le_twoLayerIn_of_isTwoComponentIn hM.1).trans hLx
      have hxM : x ∈ UnbalancedLayer.coreActionKernel M :=
        GSLit.mem_coreActionKernel_of_le_centralizer hM.1.1
      obtain ⟨K'', hK''H, hMK''⟩ := hA _ M hHtop hHbal hM.2 hMH ⟨x, hxH, hx, hxM⟩
      rw [hHcomp] at hK''H
      obtain ⟨e₁⟩ := hK''H.2.2.1
      obtain ⟨e₂⟩ := hM.2.2.1
      have hMK : M = K'' := FooteMarked.eq_of_le_of_isQuasisimple hMK'' (hQ K'' hK''H)
        (LocalCores.isQuasisimple_nontrivial (FooteMarked.Marked.quotient_quasisimple hFam hK''H.2))
        (Nat.card_congr (e₁.trans e₂.symm).toEquiv).le
      rw [hMK]
      exact hK''H
    have hne' : (FooteMarked.markedComponents 𝓢 T (centralizer ({x} : Set G))).Nonempty :=
      ⟨K', hK'x, hK'.2⟩
    exact (FooteMarked.markedLayer_le_normalizer hFam _).trans (hN _ hsub hne').2.2.2
  have hlayer : FooteMarked.markedLayer 𝓢 T (normalizer (FooteMarked.markedLayer 𝓢 T N : Set G)) =
      FooteMarked.markedLayer 𝓢 T N :=
    congrArg sSup hHcomp
  refine hE _ hHtop hHbal (by rw [hlayer]) ?_
  intro K hK x hxK hx
  rw [hHcomp] at hK
  exact hcent K hK x hxK hx

end Assembly

theorem footeIsomorphicFamilySwapExclusion_of_marked (hA : FooteMarkedAbsorption)
    (hE : FooteMarkedEmbeddingExclusion) (hS : FooteMarkedChoiceSemisimple)
    (hN : FooteMarkedChoiceNormalizer) : FooteIsomorphicFamilySwapExclusion := by
  intro G _ _ t L hmin hce hsimp hrank2 𝓢 hFam z s Y hz hs hzs hYz hY hYs
  have hset : FooteSwapSetting G t L 𝓢 :=
    ⟨hmin, hce, hsimp, hrank2, hFam, z, s, Y, hz, hs, hzs, hYz, hY, hYs⟩
  obtain ⟨N, hNc⟩ :=
    FooteMarked.exists_isMarkedChoice ⟨_, balanced_centralizer_of_swap hFam hz hzs hYz hY hYs⟩
  obtain ⟨hQ, hO⟩ := hS G t L 𝓢 hset N hNc
  exact false_of_isMarkedChoice hFam hNc (hA G t L 𝓢 hset) (hE G t L 𝓢 hset) hQ hO
    (hN G t L 𝓢 hset N hNc)

end CFSG.ComponentClassification.FooteLit
