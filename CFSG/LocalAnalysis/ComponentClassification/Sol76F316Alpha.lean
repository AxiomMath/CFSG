module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316Prod

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem concl316_map (φ : G ≃* G) {N : Subgroup G}
    (hKH : solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N)
    (hCb : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G)) :
    solomonKStarOf (normalizer (solomonKStarOf (N.map φ.toMonoidHom) : Set G)) =
        solomonKStarOf (N.map φ.toMonoidHom) ∧
      ∀ K ∈ kStarComponents (N.map φ.toMonoidHom), ∀ s ∈ K, orderOf s = 2 →
        centralizer ({s} : Set G) ≤
          normalizer (solomonKStarOf (N.map φ.toMonoidHom) : Set G) := by
  have hN : normalizer (solomonKStarOf (N.map φ.toMonoidHom) : Set G) =
      (normalizer (solomonKStarOf N : Set G)).map φ.toMonoidHom := by
    rw [← Sol76.map_solomonKStarOf φ N, Subgroup.map_equiv_normalizer_eq]
  refine ⟨?_, ?_⟩
  · rw [hN, ← Sol76.map_solomonKStarOf φ, hKH, Sol76.map_solomonKStarOf φ]
  · rw [Sol76.kStarComponents_map φ N]
    rintro _ ⟨K, hK, rfl⟩ _ ⟨s, hs, rfl⟩ hs2
    have hs2' : orderOf s = 2 := by
      rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hs2
    have hc : centralizer ({φ.toMonoidHom s} : Set G) =
        (centralizer ({s} : Set G)).map φ.toMonoidHom := by
      have h1 := Sol76.map_centralizer φ (zpowers s)
      rw [MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure, zpowers_eq_closure,
        centralizer_closure] at h1
      exact h1.symm
    rw [hN, hc]
    exact map_mono (hCb K hK s hs hs2')

theorem eq_of_sup_oddCoreIn_eq_components {M₁ M₂ K₁ K₂ Y : Subgroup G}
    (hK₁ : IsTwoComponentIn K₁ M₁) (hK₂ : IsTwoComponentIn K₂ M₂)
    (hC₁ : ∀ s ∈ K₁, orderOf s = 2 → centralizer ({s} : Set G) ≤ M₁)
    (hC₂ : ∀ s ∈ K₂, orderOf s = 2 → centralizer ({s} : Set G) ≤ M₂)
    (hYK₁ : Y ≤ K₁) (hYK₂ : Y ≤ K₂) (hY₁ : Y ⊔ oddCoreIn K₁ = K₁)
    (hY₂ : Y ⊔ oddCoreIn K₂ = K₂) (hYr : 2 ≤ CFSG.Open.pRank 2 Y)
    (hYperf : ⁅Y, Y⁆ = Y) : K₁ = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC₁Y : ∀ y ∈ Y, orderOf y = 2 → centralizer ({y} : Set G) ≤ M₁ := fun y hy hy2 =>
    hC₁ y (hYK₁ hy) hy2
  have hC₂Y : ∀ y ∈ Y, orderOf y = 2 → centralizer ({y} : Set G) ≤ M₂ := fun y hy hy2 =>
    hC₂ y (hYK₂ hy) hy2
  have hYM₁ : Y ≤ M₁ := hYK₁.trans hK₁.1
  have hYM₂ : Y ≤ M₂ := hYK₂.trans hK₂.1
  have hO₁ : oddCoreIn M₁ ≤ M₂ :=
    le_of_coprime_of_pRank hYr hC₂Y (coprime_card_oddCoreIn M₁)
      (hYM₁.trans (le_normalizer_oddCoreIn M₁))
  have hO₂ : oddCoreIn M₂ ≤ M₁ :=
    le_of_coprime_of_pRank hYr hC₁Y (coprime_card_oddCoreIn M₂)
      (hYM₂.trans (le_normalizer_oddCoreIn M₂))
  have hK₁M₂ : K₁ ≤ M₂ := by
    rw [← hY₁]
    exact sup_le hYM₂ ((oddCoreIn_le_of_isTwoComponentIn hK₁).trans hO₁)
  have hK₂M₁ : K₂ ≤ M₁ := by
    rw [← hY₂]
    exact sup_le hYM₁ ((oddCoreIn_le_of_isTwoComponentIn hK₂).trans hO₂)
  have hK₁C : IsTwoComponentIn K₁ (M₁ ⊓ M₂) :=
    ⟨le_inf hK₁.1 hK₁M₂, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (le_inf hK₁.1 hK₁M₂) inf_le_left hK₁.2⟩
  have hK₂C : IsTwoComponentIn K₂ (M₁ ⊓ M₂) :=
    ⟨le_inf hK₂M₁ hK₂.1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (le_inf hK₂M₁ hK₂.1) inf_le_right hK₂.2⟩
  by_contra hne
  have h := GSThmB.B5a.le_coreActionKernel_of_ne hK₁C.1 hK₂C.1 hK₁C.2 hK₂C.2 hne
  obtain ⟨y, hy, hy2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hYr)
  exact not_le_coreActionKernel_of_le hYK₁ hYperf ⟨y, hy, hy2⟩ (hYK₂.trans h)

theorem eq_of_sup_oddCoreIn_eq {N₁ N₂ : Subgroup G}
    (hCb₁ : ∀ K ∈ kStarComponents N₁, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N₁ : Set G))
    (hCb₂ : ∀ K ∈ kStarComponents N₂, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N₂ : Set G))
    {K₁ K₂ Y : Subgroup G} (hK₁ : K₁ ∈ kStarComponents N₁) (hK₂ : K₂ ∈ kStarComponents N₂)
    (hYK₁ : Y ≤ K₁) (hYK₂ : Y ≤ K₂) (hY₁ : Y ⊔ oddCoreIn K₁ = K₁) (hY₂ : Y ⊔ oddCoreIn K₂ = K₂)
    (hYr : 2 ≤ CFSG.Open.pRank 2 Y) (hYperf : ⁅Y, Y⁆ = Y) : K₁ = K₂ :=
  eq_of_sup_oddCoreIn_eq_components
    (mem_kStarComponents_normalizer hK₁).1 (mem_kStarComponents_normalizer hK₂).1
    (fun s hs hs2 => hCb₁ K₁ hK₁ s hs hs2)
    (fun s hs hs2 => hCb₂ K₂ hK₂ s hs hs2)
    hYK₁ hYK₂ hY₁ hY₂ hYr hYperf

theorem exists_mem_kStarComponents_of_mem_coreActionKernel (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {N₁ N₂ : Subgroup G}
    (hr₁ : ∃ K₁ ∈ kStarComponents N₁, ∃ K₂ ∈ kStarComponents N₁, K₁ ≠ K₂)
    (hKH₁ : solomonKStarOf (normalizer (solomonKStarOf N₁ : Set G)) = solomonKStarOf N₁)
    (hCb₁ : ∀ K ∈ kStarComponents N₁, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N₁ : Set G))
    (hCb₂ : ∀ K ∈ kStarComponents N₂, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N₂ : Set G))
    {K L : Subgroup G} (hK : K ∈ kStarComponents N₁) (hL : L ∈ kStarComponents N₂) {s : G}
    (hsK : s ∈ K) (hs2 : orderOf s = 2) (hsL : s ∈ coreActionKernel L) :
    ∃ K₀ ∈ kStarComponents N₁, K₀ ∈ kStarComponents N₂ := by
  set Cs := centralizer ({s} : Set G) with hCs
  have hY := isTwoComponentIn_twoLayerIn_inf_centralizer hq hG hCb₂ hL hs2 hsL
  obtain ⟨K₀, hK₀, hsK₀, heq⟩ :=
    exists_eq_twoLayerIn_inf_of_mem_kStarComponents hq hG hr₁ hKH₁ hCb₁ hK hsK hs2 hY
  obtain ⟨hL2, hLsup, -, -, hLr⟩ := pump_facts hL hsL hs2
  obtain ⟨hK₀2, hK₀sup, -, -, -⟩ := pump_facts hK₀ hsK₀ hs2
  have hYperf : ⁅twoLayerIn (L ⊓ Cs), twoLayerIn (L ⊓ Cs)⁆ = twoLayerIn (L ⊓ Cs) :=
    UnbalancedCorr.commutator_eq_of_isPComponent hL2.1 hL2.2
  have hYK₀ : twoLayerIn (L ⊓ Cs) ≤ K₀ := by
    rw [heq]
    exact hK₀2.1.trans inf_le_left
  have hY₀ : twoLayerIn (L ⊓ Cs) ⊔ oddCoreIn K₀ = K₀ := by
    rw [heq]
    exact hK₀sup
  have hK₀L : K₀ = L := eq_of_sup_oddCoreIn_eq hCb₁ hCb₂ hK₀ hL hYK₀
    (hL2.1.trans inf_le_left) hY₀ hLsup hLr hYperf
  exact ⟨K₀, hK₀, hK₀L ▸ hL⟩

theorem kStarComponents_subset_of_mem_of_mem (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {N₁ N₂ : Subgroup G}
    (hr₂ : ∃ K₁ ∈ kStarComponents N₂, ∃ K₂ ∈ kStarComponents N₂, K₁ ≠ K₂)
    (hKH₂ : solomonKStarOf (normalizer (solomonKStarOf N₂ : Set G)) = solomonKStarOf N₂)
    (hCb₁ : ∀ K ∈ kStarComponents N₁, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N₁ : Set G))
    (hCb₂ : ∀ K ∈ kStarComponents N₂, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N₂ : Set G))
    {K₀ : Subgroup G} (hK₁ : K₀ ∈ kStarComponents N₁) (hK₂ : K₀ ∈ kStarComponents N₂) :
    kStarComponents N₁ ⊆ kStarComponents N₂ := by
  intro J hJ
  by_cases hJK : J = K₀
  · rw [hJK]
    exact hK₂
  obtain ⟨w, hwK₀, hw2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK₁.2
  set Cw := centralizer ({w} : Set G) with hCw
  have hwJ : w ∈ coreActionKernel J := mem_coreActionKernel_of_ne hK₁ hJ (Ne.symm hJK) hwK₀
  have hJw := isTwoComponentIn_twoLayerIn_inf_centralizer hq hG hCb₁ hJ hw2 hwJ
  obtain ⟨J', hJ', hwJ', heq⟩ :=
    exists_eq_twoLayerIn_inf_of_mem_kStarComponents hq hG hr₂ hKH₂ hCb₂ hK₂ hwK₀ hw2 hJw
  obtain ⟨hJw2, hJwsup, -, -, hJwr⟩ := pump_facts hJ hwJ hw2
  obtain ⟨hJ'w2, hJ'wsup, -, -, -⟩ := pump_facts hJ' hwJ' hw2
  have hYperf : ⁅twoLayerIn (J ⊓ Cw), twoLayerIn (J ⊓ Cw)⁆ = twoLayerIn (J ⊓ Cw) :=
    UnbalancedCorr.commutator_eq_of_isPComponent hJw2.1 hJw2.2
  have hYJ' : twoLayerIn (J ⊓ Cw) ≤ J' := by
    rw [heq]
    exact hJ'w2.1.trans inf_le_left
  have hY' : twoLayerIn (J ⊓ Cw) ⊔ oddCoreIn J' = J' := by
    rw [heq]
    exact hJ'wsup
  have hJJ' : J = J' := eq_of_sup_oddCoreIn_eq hCb₁ hCb₂ hJ hJ' (hJw2.1.trans inf_le_left) hYJ'
    hJwsup hY' hJwr hYperf
  exact hJJ' ▸ hJ'

theorem mem_normalizer_of_caseAlpha_modO (hq : QuasisimpleTwoPartInput) (hG : KStarKProper G)
    {N : Subgroup G} (hr : ∃ K₁ ∈ kStarComponents N, ∃ K₂ ∈ kStarComponents N, K₁ ≠ K₂)
    (hKH : solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N)
    (hCb : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G)) {g : G}
    (h : (∃ K ∈ kStarComponents N, ∃ s ∈ K, orderOf s = 2 ∧
          ∃ L ∈ kStarComponents N, s ∈ coreActionKernel (conjugate L g)) ∨
        (∃ L ∈ kStarComponents N, ∃ s ∈ conjugate L g, orderOf s = 2 ∧
          ∃ K ∈ kStarComponents N, s ∈ coreActionKernel K)) :
    g ∈ normalizer (solomonKStarOf N : Set G) := by
  have hconj : ∀ L ∈ kStarComponents N, conjugate L g ∈ kStarComponents (conjugate N g) := by
    intro L hL
    rw [kStarComponents_conjugate]
    exact ⟨L, hL, rfl⟩
  have hrg : ∃ K₁ ∈ kStarComponents (conjugate N g), ∃ K₂ ∈ kStarComponents (conjugate N g),
      K₁ ≠ K₂ := by
    obtain ⟨K₁, h₁, K₂, h₂, hne⟩ := hr
    exact ⟨conjugate K₁ g, hconj K₁ h₁, conjugate K₂ g, hconj K₂ h₂,
      fun h => hne (Subgroup.map_injective (MulAut.conj g⁻¹).injective h)⟩
  obtain ⟨hKHg, hCbg⟩ := concl316_map (MulAut.conj g⁻¹) hKH hCb
  change solomonKStarOf (normalizer (solomonKStarOf (conjugate N g) : Set G)) =
    solomonKStarOf (conjugate N g) at hKHg
  change ∀ K ∈ kStarComponents (conjugate N g), ∀ s ∈ K, orderOf s = 2 →
    centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf (conjugate N g) : Set G) at hCbg
  have hkey : kStarComponents N = kStarComponents (conjugate N g) := by
    rcases h with ⟨K, hK, s, hsK, hs2, L, hL, hsL⟩ | ⟨L, hL, s, hsL, hs2, K, hK, hsK⟩
    · obtain ⟨K₀, h₁, h₂⟩ := exists_mem_kStarComponents_of_mem_coreActionKernel hq hG hr hKH hCb
        hCbg hK (hconj L hL) hsK hs2 hsL
      exact Set.Subset.antisymm
        (kStarComponents_subset_of_mem_of_mem hq hG hrg hKHg hCb hCbg h₁ h₂)
        (kStarComponents_subset_of_mem_of_mem hq hG hr hKH hCbg hCb h₂ h₁)
    · obtain ⟨K₀, h₁, h₂⟩ := exists_mem_kStarComponents_of_mem_coreActionKernel hq hG hrg hKHg
        hCbg hCb (hconj L hL) hK hsL hs2 hsK
      exact Set.Subset.antisymm
        (kStarComponents_subset_of_mem_of_mem hq hG hrg hKHg hCb hCbg h₂ h₁)
        (kStarComponents_subset_of_mem_of_mem hq hG hr hKH hCbg hCb h₁ h₂)
  have hD : conjugate (solomonKStarOf N) g = solomonKStarOf N := by
    rw [conjugate_solomonKStarOf, solomonKStarOf_eq_sSup (conjugate N g), ← hkey,
      ← solomonKStarOf_eq_sSup N]
  have hginv : g⁻¹ ∈ normalizer (solomonKStarOf N : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr hD
  simpa using inv_mem hginv

end CFSG.ComponentClassification.Sol76T13
