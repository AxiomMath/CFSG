module

public import CFSG.ClassicalInvolution.Asc77.AscSix69

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_member_of_mem_USet' {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ J ∈ Ω, U ≤ J := by
  obtain ⟨R, hR, hUR, -, -⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact ⟨J, hJ, hUR.trans hRJ.1⟩

theorem mem_etaSet_of_cover_of [Finite G]
    (hUn : ∀ U ∈ USet Ω, ∀ J ∈ Ω, ∀ J' ∈ Ω, U ≤ J → U ≤ J' → J = J')
    {S : Subgroup G} {η : Set (Subgroup G)} (hsub : η ⊆ UinS Ω S) (hd : InDistinctMembers Ω η)
    (hcov : ∀ K ∈ Ω, (∃ U ∈ UinS Ω S, U ≤ K) → ∃ V ∈ η, V ≤ K) : η ∈ etaSet Ω S := by
  classical
  refine ⟨hsub, hd, fun η' hη' hd' => ?_⟩
  have hex : ∀ U' ∈ η', ∃ V ∈ η, ∃ K ∈ Ω, U' ≤ K ∧ V ≤ K := by
    intro U' hU'
    obtain ⟨K, hK, hU'K⟩ := exists_member_of_mem_USet' (hη' hU').1
    obtain ⟨V, hV, hVK⟩ := hcov K hK ⟨U', hη' hU', hU'K⟩
    exact ⟨V, hV, K, hK, hU'K, hVK⟩
  choose! g hgη hgK using hex
  refine Set.ncard_le_ncard_of_injOn g hgη ?_ (Set.toFinite η)
  intro U₁ h₁ U₂ h₂ heq
  by_contra hne
  obtain ⟨K₁, hK₁, hU₁K₁, hgK₁⟩ := hgK U₁ h₁
  obtain ⟨K₂, hK₂, hU₂K₂, hgK₂⟩ := hgK U₂ h₂
  have hV : g U₁ ∈ USet Ω := (hsub (hgη U₁ h₁)).1
  have hK12 : K₁ = K₂ := hUn _ hV K₁ hK₁ K₂ hK₂ hgK₁ (heq ▸ hgK₂)
  exact hd' U₁ h₁ U₂ h₂ hne K₁ hK₁ ⟨hU₁K₁, hK12 ▸ hU₂K₂⟩

theorem exists_invariant_mem_etaSet_of [Finite G] (hΩc : ConjInvariant Ω)
    (hUn : ∀ U ∈ USet Ω, ∀ J ∈ Ω, ∀ J' ∈ Ω, U ≤ J → U ≤ J' → J = J')
    (hInv : ∀ K ∈ Ω, ∀ T P : Subgroup G, IsSylow2In T K → IsPGroup 2 P → T ≤ P →
      (∀ q ∈ P, conjSub q T = T) → ∃ U ∈ USet Ω, U ≤ T ∧ ∀ q ∈ P, conjSub q U = U)
    (S : Sylow 2 G) :
    ∃ η ∈ etaSet Ω (S : Subgroup G), ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η := by
  classical
  set 𝒮 : Subgroup G := (S : Subgroup G) with h𝒮
  have h𝒮2 : IsPGroup 2 𝒮 := S.isPGroup'
  let Adm : Set (Set (Subgroup G)) :=
    {η | η ⊆ UinS Ω 𝒮 ∧ (∀ s ∈ 𝒮, ∀ U ∈ η, conjSub s U ∈ η) ∧ InDistinctMembers Ω η}
  have hAdm : Adm.Nonempty :=
    ⟨∅, Set.empty_subset _, fun s _ U hU => absurd hU (Set.notMem_empty U),
      fun U hU => absurd hU (Set.notMem_empty U)⟩
  obtain ⟨η, hηA, hmax⟩ := Set.exists_max_image Adm (fun η => η.ncard) (Set.toFinite Adm) hAdm
  refine ⟨η, ?_, hηA.2.1⟩
  refine mem_etaSet_of_cover_of hUn hηA.1 hηA.2.2 ?_
  rintro K hK ⟨U₀, hU₀, hU₀K⟩
  by_contra hno
  push Not at hno
  set N : Subgroup G := 𝒮 ⊓ Subgroup.normalizer (K : Set G) with hNdef
  set T : Subgroup G := K ⊓ 𝒮 with hTdef
  have hN2 : IsPGroup 2 N := h𝒮2.to_le inf_le_left
  have hTN : T ≤ N := fun x hx =>
    ⟨hx.2, mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_self_of_mem hx.1)⟩
  have hTn : ∀ q ∈ N, conjSub q T = T := by
    intro q hq
    rw [hTdef, conjSub_inf, mem_normalizer_iff_conjSub_eq.mp hq.2, conjSub_eq_self_of_mem hq.1]
  have hT2 : IsPGroup 2 T := h𝒮2.to_le inf_le_right
  have hTK : T ≤ K := inf_le_left
  have hU₀T : U₀ ≤ T := le_inf hU₀K hU₀.2
  have key : ∃ U₁ ∈ USet Ω, U₁ ≤ T ∧ ∀ q ∈ N, conjSub q U₁ = U₁ := by
    obtain ⟨R₀, hR₀, hU₀R₀, -, hidx⟩ := hU₀.1
    obtain ⟨J, hJ, hR₀J⟩ := exists_isSylow2In_of_mem_RSet hR₀
    have hJK : J = K := hUn U₀ hU₀.1 J hJ K hK (hU₀R₀.trans hR₀J.1) hU₀K
    subst hJK
    have hR₀card : Nat.card R₀ = 2 * Nat.card U₀ := by
      have h1 := Subgroup.relIndex_mul_card (H := U₀) (K := R₀)
      rw [hidx, inf_eq_left.mpr hU₀R₀] at h1
      exact h1.symm
    obtain ⟨R₁, hR₁, hTR₁⟩ := IsSylow2In.exists_ge hT2 hTK
    have hR₁card : Nat.card R₁ = 2 * Nat.card U₀ := by rw [← hR₀card, hR₁.natCard_eq hR₀J]
    rcases eq_or_eq_of_natCard_eq_two_mul hU₀T hTR₁ hR₁card with hTeq | hTeq
    · refine ⟨U₀, hU₀.1, hU₀T, fun q hq => ?_⟩
      have := hTn q hq
      rwa [hTeq] at this
    · exact hInv J hK T N (hTeq ▸ hR₁) hN2 hTN hTn
  obtain ⟨U₁, hU₁, hU₁T, hU₁inv⟩ := key
  have hU₁K : U₁ ≤ K := hU₁T.trans hTK
  have hU₁S : U₁ ∈ UinS Ω 𝒮 := ⟨hU₁, hU₁T.trans inf_le_right⟩
  set orb : Set (Subgroup G) := {V | ∃ s ∈ 𝒮, V = conjSub s U₁} with horb
  have horb_sub : orb ⊆ UinS Ω 𝒮 := by
    rintro _ ⟨s, hs, rfl⟩
    exact UinS.conj hΩc hU₁S hs
  have hmem : ∀ s ∈ 𝒮, ∀ J ∈ Ω, conjSub s U₁ ≤ J → J = conjSub s K := fun s hs J hJ hle =>
    hUn _ (USet.conj hΩc hU₁ s) J hJ _ (hΩc s K hK) hle (conjSub_mono hU₁K)
  have hinvη : ∀ s ∈ 𝒮, ∀ V ∈ η, conjSub s V ∈ η := hηA.2.1
  have hcov : ∀ s ∈ 𝒮, ∀ V ∈ η, ¬ V ≤ conjSub s K := by
    intro s hs V hV hle
    have h1 : conjSub s⁻¹ V ≤ K := by
      have := conjSub_mono (n := s⁻¹) hle
      rwa [conjSub_inv_conjSub] at this
    exact hno _ (hinvη s⁻¹ (𝒮.inv_mem hs) V hV) h1
  have hη'A : η ∪ orb ∈ Adm := by
    refine ⟨Set.union_subset hηA.1 horb_sub, ?_, ?_⟩
    · intro s hs V hV
      rcases hV with hV | ⟨t, ht, rfl⟩
      · exact Or.inl (hinvη s hs V hV)
      · exact Or.inr ⟨s * t, 𝒮.mul_mem hs ht, (conjSub_mul s t U₁).symm⟩
    · intro V₁ hV₁ V₂ hV₂ hne J hJ hVJ
      rcases hV₁ with hV₁ | ⟨s, hs, rfl⟩ <;> rcases hV₂ with hV₂ | ⟨t, ht, rfl⟩
      · exact hηA.2.2 V₁ hV₁ V₂ hV₂ hne J hJ hVJ
      · have hJ' := hmem t ht J hJ hVJ.2
        exact hcov t ht V₁ hV₁ (hJ' ▸ hVJ.1)
      · have hJ' := hmem s hs J hJ hVJ.1
        exact hcov s hs V₂ hV₂ (hJ' ▸ hVJ.2)
      · have h1 := hmem s hs J hJ hVJ.1
        have h2 := hmem t ht J hJ hVJ.2
        have hKst : conjSub t K = conjSub s K := h2.symm.trans h1
        have hst : conjSub (s⁻¹ * t) K = K := by
          rw [conjSub_mul, hKst, conjSub_inv_conjSub]
        have hmemN : s⁻¹ * t ∈ N :=
          ⟨𝒮.mul_mem (𝒮.inv_mem hs) ht, mem_normalizer_iff_conjSub_eq.mpr hst⟩
        have h3 := hU₁inv _ hmemN
        apply hne
        calc conjSub s U₁ = conjSub s (conjSub (s⁻¹ * t) U₁) := by rw [h3]
          _ = conjSub (s * (s⁻¹ * t)) U₁ := (conjSub_mul s _ U₁).symm
          _ = conjSub t U₁ := by rw [mul_inv_cancel_left]
  have hss : η ⊂ η ∪ orb := by
    refine Set.ssubset_def.mpr ⟨Set.subset_union_left, fun hsub => ?_⟩
    have hU₁orb : U₁ ∈ orb := ⟨1, 𝒮.one_mem, (conjSub_one U₁).symm⟩
    exact hno U₁ (hsub (Or.inr hU₁orb)) hU₁K
  have h1 : (η ∪ orb).ncard ≤ η.ncard := hmax _ hη'A
  have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
  omega

theorem exists_mem_WSet_le_of [Finite G] (hΩc : ConjInvariant Ω)
    (hUn : ∀ U ∈ USet Ω, ∀ J ∈ Ω, ∀ J' ∈ Ω, U ≤ J → U ≤ J' → J = J')
    (hInv : ∀ K ∈ Ω, ∀ T P : Subgroup G, IsSylow2In T K → IsPGroup 2 P → T ≤ P →
      (∀ q ∈ P, conjSub q T = T) → ∃ U ∈ USet Ω, U ≤ T ∧ ∀ q ∈ P, conjSub q U = U)
    (S : Sylow 2 G) : ∃ W ∈ WSet Ω, W ≤ (S : Subgroup G) := by
  obtain ⟨η, hη, hinv⟩ := exists_invariant_mem_etaSet_of hΩc hUn hInv S
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
