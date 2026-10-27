module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigH

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

theorem exists_isKleinFour_le {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) : ∃ E : Subgroup G, E ≤ B ∧ IsKleinFour E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 2 (n := 2)
    (by rw [hB8]; norm_num)
  refine ⟨E₀.map B.subtype, map_subtype_le _, isKleinFour_of_card_eq_four ?_ ?_⟩
  · rw [card_map_of_injective B.subtype_injective, hE₀]; norm_num
  · rintro _ ⟨x, -, rfl⟩
    exact hB.2 x x.2

theorem isPGroup_sup_of_le_centralizer {B V : Subgroup G} (hB2 : IsPGroup 2 B)
    (hV2 : IsPGroup 2 V) (hBV : B ≤ centralizer (V : Set G)) : IsPGroup 2 (B ⊔ V : Subgroup G) :=
  IsPGroup.to_sup_of_normal_right' hB2 hV2
    (hBV.trans (Subgroup.centralizer_le_normalizer (V : Set G)))

theorem le_normalizer_of_mem_kStarComponents (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) : K ≤ normalizer (K' : Set G) :=
  (le_twoLayerIn_of_isTwoComponentIn hK.1).trans (twoLayerIn_le_normalizer hK'.1.1 hK'.1.2)

theorem le_normalizer_wGroup_of_ne (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N)
    (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K') :
    K'' ≤ normalizer (wGroup B V : Set G) := by
  have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
  have hV2 := isPGroup_of_isKleinFour hV
  have hS2 := isPGroup_sup_of_le_centralizer hB2 hV2 hBV
  have hSQ : B ⊔ V ≤ coreActionKernel K'' :=
    sup_le (hBK.trans (le_coreActionKernel_of_ne hK'' hK hK''K))
      (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K'))
  have hcov := inf_centralizer_sup_oddCoreIn_eq hS2 hSQ
  obtain ⟨E, hEB, hE⟩ := exists_isKleinFour_le hB hB8
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra h
    push Not at h
    have : V = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h x hx)
    have h4 := hV.card_four
    rw [this, card_bot] at h4
    norm_num at h4
  rw [← hcov]
  refine sup_le ?_ ?_
  ·
    intro x hx
    have hxS : x ∈ centralizer ((B ⊔ V : Subgroup G) : Set G) := hx.2
    have hxB : x ∈ centralizer (B : Set G) := centralizer_le (by exact_mod_cast le_sup_left) hxS
    have hxV : x ∈ centralizer (V : Set G) := centralizer_le (by exact_mod_cast le_sup_right) hxS
    have hxE : x ∈ normalizer (E : Set G) :=
      Subgroup.centralizer_le_normalizer (E : Set G) (centralizer_le (by exact_mod_cast hEB) hxB)
    have hxv : x ∈ centralizer ({v} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.mpr hv) hxV
    exact le_normalizer_wGroup_of_mem h32 hG hN hK hK' hne hV hVK' hBK hBV hB hE hEB hv hv1 hxE
      hxv
  ·
    refine le_normalizer_wGroup_of_odd h32 hG hN hK hK' hne hV hVK' hBK hBV hB hB8
      (coprime_card_oddCoreIn K'') ?_ ?_
    · exact fun b hb => mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_oddCoreIn (le_normalizer_of_mem_kStarComponents hK hK'' (hBK hb)))
    · exact fun w hw => mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_oddCoreIn (le_normalizer_of_mem_kStarComponents hK' hK'' (hVK' hw)))

theorem oddCoreIn_le_normalizer_wGroup (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) : oddCoreIn N ≤ normalizer (wGroup B V : Set G) := by
  have hKN : K ≤ N := hK.1.1
  have hK'N : K' ≤ N := hK'.1.1
  refine le_normalizer_wGroup_of_odd h32 hG hN hK hK' hne hV hVK' hBK hBV hB hB8
    (coprime_card_oddCoreIn N) ?_ ?_
  · exact (hBK.trans hKN).trans (le_normalizer_oddCoreIn N)
  · exact (hVK'.trans hK'N).trans (le_normalizer_oddCoreIn N)

end CFSG.ComponentClassification.Sol76.Sig
