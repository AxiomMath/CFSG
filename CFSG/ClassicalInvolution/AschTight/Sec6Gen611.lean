module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen69
public import CFSG.ClassicalInvolution.AschTight.Sec6GenCyc66
public import CFSG.ClassicalInvolution.AschTight.Sec6GenTargets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

section Finite

variable [Finite G]

theorem exists_mem_UinS_of_two_lt (hΩ : HypOmegaGen Ω)
    (hC : Cyc66 Ω) (S : Sylow 2 G) {K : Subgroup G} (hK : K ∈ Ω)
    (h2 : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) :
    ∃ U ∈ UinS Ω (S : Subgroup G), U ≤ K := by
  by_contra hno
  push Not at hno
  have hΩc := hΩ.conjInvariant
  set 𝒮 : Subgroup G := (S : Subgroup G) with h𝒮
  have h𝒮2 : IsPGroup 2 𝒮 := S.isPGroup'
  obtain ⟨β, hβ, hβinv⟩ := exists_invariant_mem_etaSet hΩ S
  obtain ⟨habel, hUW⟩ := eta_abelian_of_cyc66 hΩ hC hβ hβinv
  have hβK : ∀ V ∈ β, ¬ V ≤ K := fun V hV hle => hno V (hβ.1 hV) hle
  have hAW : ∀ A ∈ β, A ≤ ⨆ U ∈ β, U := fun A hA => le_iSup₂_of_le A hA le_rfl
  set N : Subgroup G := 𝒮 ⊓ Subgroup.normalizer (K : Set G) with hNdef
  set T : Subgroup G := K ⊓ 𝒮 with hTdef
  have hN2 : IsPGroup 2 N := h𝒮2.to_le inf_le_left
  have hTN : T ≤ N := fun x hx =>
    ⟨hx.2, mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_self_of_mem hx.1)⟩
  have hTn : ∀ q ∈ N, conjSub q T = T := fun q hq => conjSub_inf_of_mem_inf_normalizer hq
  have hT2 : IsPGroup 2 ↥T := h𝒮2.to_inf_right
  have hTK : T ≤ K := inf_le_left
  have hT4 : 4 ≤ Nat.card T := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      _ = Nat.card T := hn.symm
  obtain ⟨zK, hzK⟩ := exists_uniqueInvolution hΩ hK
  have hzT : zK ∈ T := mem_of_isUniqueInvolution_of_isPGroup hzK hTK hT2 (by omega)
  have huniq : IsUniqueInvolution T zK :=
    ⟨hzT, hzK.ne_one, hzK.sq, fun y hy hy2 => hzK.unique y (hTK hy) hy2⟩
  obtain ⟨A, hAT, hAcyc, hAcard, hAinv⟩ :=
    exists_invariant_cyclic_order_four hN2 hTN hTn huniq hT4
  have hAK : A ≤ K := hAT.trans hTK
  have hAS : A ≤ 𝒮 := hAT.trans inf_le_right
  have hA2 : IsPGroup 2 ↥A := IsPGroup.of_card (n := 2) (by rw [hAcard]; norm_num)
  have hzA : zK ∈ A := mem_of_isUniqueInvolution_of_isPGroup hzK hAK hA2 (by omega)
  set orb : Set (Subgroup G) := {B | ∃ s ∈ 𝒮, B = conjSub s A} with horb
  have hmem : ∀ s ∈ 𝒮, ∀ J ∈ Ω, conjSub s A ≤ J → J = conjSub s K := by
    intro s hs J hJ hle
    have hA4 : 4 ≤ Nat.card (conjSub s A) := by rw [natCard_conjSub, hAcard]
    have hA2' : IsPGroup 2 ↥(conjSub s A) := isPGroup_conjSub s hA2
    exact eq_of_le_of_le hΩ hJ (hΩc s K hK) hA2' hA4 hle (conjSub_mono hAK)
  have hcov : ∀ s ∈ 𝒮, ∀ V ∈ β, ¬ V ≤ conjSub s K := by
    intro s hs V hV hle
    have h1 : conjSub s⁻¹ V ≤ K := by
      have := conjSub_mono (n := s⁻¹) hle
      rwa [conjSub_inv_conjSub] at this
    exact hβK _ (hβinv s⁻¹ (𝒮.inv_mem hs) V hV) h1
  have hkey : Commutes A (⨆ U ∈ β, U) := by
    have hcomm : ∀ V ∈ β, Commutes A V := by
      intro V hV
      refine hC 𝒮 h𝒮2 (β ∪ orb) ?_ ?_ ?_ ?_ A (Or.inr ⟨1, 𝒮.one_mem, (conjSub_one A).symm⟩) V
        (Or.inl hV) ?_
      · rintro B (hB | ⟨s, hs, rfl⟩)
        · exact (hβ.1 hB).2
        · exact conjSub_le_of_le_of_mem hAS hs
      · rintro B (hB | ⟨t, ht, rfl⟩) s hs
        · exact Or.inl (hβinv s hs B hB)
        · exact Or.inr ⟨s * t, 𝒮.mul_mem hs ht, (conjSub_mul s t A).symm⟩
      · rintro B (hB | ⟨s, hs, rfl⟩)
        · obtain ⟨R, -, J, -, -, -, hcyc, -, h4⟩ := exists_data_of_mem_USet hΩ (hβ.1 hB).1
          exact ⟨hcyc, h4⟩
        · exact ⟨isCyclic_conjSub hAcyc s, by rw [natCard_conjSub, hAcard]⟩
      · intro B hB B' hB' hne
        have hmemΩ : ∀ B ∈ β ∪ orb, ∃ J ∈ Ω, B ≤ J := by
          rintro B (hB | ⟨s, hs, rfl⟩)
          · exact exists_member_of_mem_USet hΩ (hβ.1 hB).1
          · exact ⟨conjSub s K, hΩc s K hK, conjSub_mono hAK⟩
        obtain ⟨J, hJ, hBJ⟩ := hmemΩ B hB
        obtain ⟨J', hJ', hBJ'⟩ := hmemΩ B' hB'
        refine ⟨J, hJ, J', hJ', fun hJJ => ?_, hBJ, hBJ'⟩
        subst hJJ
        rcases hB with hB | ⟨s, hs, rfl⟩ <;> rcases hB' with hB' | ⟨t, ht, rfl⟩
        · exact hβ.2.1 B hB B' hB' hne J hJ ⟨hBJ, hBJ'⟩
        · exact hcov t ht B hB (hmem t ht J hJ hBJ' ▸ hBJ)
        · exact hcov s hs B' hB' (hmem s hs J hJ hBJ ▸ hBJ')
        · have h1 := hmem s hs J hJ hBJ
          have h2 := hmem t ht J hJ hBJ'
          have hKst : conjSub t K = conjSub s K := h2.symm.trans h1
          have hst : conjSub (s⁻¹ * t) K = K := by
            rw [conjSub_mul, hKst, conjSub_inv_conjSub]
          have hmemN : s⁻¹ * t ∈ N :=
            ⟨𝒮.mul_mem (𝒮.inv_mem hs) ht, mem_normalizer_iff_conjSub_eq.mpr hst⟩
          have h3 := hAinv _ hmemN
          apply hne
          calc conjSub s A = conjSub s (conjSub (s⁻¹ * t) A) := by rw [h3]
            _ = conjSub (s * (s⁻¹ * t)) A := (conjSub_mul s _ A).symm
            _ = conjSub t A := by rw [mul_inv_cancel_left]
      · intro hAV
        exact hβK V hV (hAV ▸ hAK)
    intro x hx y hy
    have h1 : (⨆ U ∈ β, U) ≤ Subgroup.centralizer (A : Set G) := by
      refine iSup₂_le fun V hV v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcomm V hV a ha v hv)
    exact (Subgroup.mem_centralizer_iff.mp (h1 hy) x hx)
  have hWK : (⨆ U ∈ β, U) ≤ Subgroup.normalizer (K : Set G) := by
    refine iSup₂_le fun V hV => ?_
    have hVU : V ∈ USet Ω := (hβ.1 hV).1
    obtain ⟨J, hJ, hVJ⟩ := exists_member_of_mem_USet hΩ hVU
    have hKJ : K ≠ J := by
      rintro rfl
      exact hβK V hV hVJ
    have hV4 : 4 ≤ Nat.card V := by
      obtain ⟨R, -, J', -, -, -, -, -, h4⟩ := exists_data_of_mem_USet hΩ hVU
      exact h4
    have hVc : V ≤ Subgroup.centralizer ({zK} : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hkey zK (hzA) v (hAW V hV hv)).symm
    exact le_normalizer_of_le_centralizer hΩ hK hJ hKJ hzK hVJ
      (isPGroup_of_mem_USet hΩ hVU) (by omega) hVc
  have hW2 : IsPGroup 2 ↥(⨆ U ∈ β, U) := h𝒮2.to_le (iSup₂_le fun V hV => (hβ.1 hV).2)
  obtain ⟨R, hR, hRfix⟩ := AscL62.exists_sylow_normalized hW2 hWK
  have hRW : (⨆ U ∈ β, U) ≤ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  have hSig : IsPGroup 2 ↥(R ⊔ (⨆ U ∈ β, U)) := IsPGroup.to_sup_of_normal_left' hR.2.1 hW2 hRW
  obtain ⟨S', hS'⟩ := IsPGroup.exists_le_sylow hSig
  obtain ⟨U, hUR, hUcyc, hUcard⟩ :=
    (isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)).exists_cyclic_index_two
  have hU : U ∈ USet Ω := mem_USet_of_natCard hK hR hUR hUcyc hUcard
  have hUS' : U ≤ (S' : Subgroup G) := hUR.trans (le_sup_left.trans hS')
  have hβS' : ∀ V ∈ β, V ≤ (S' : Subgroup G) := fun V hV =>
    (hAW V hV).trans (le_sup_right.trans hS')
  have hβ' : β ∈ etaSet Ω (S' : Subgroup G) := mem_etaSet_of_le hΩc hβ hβS'
  obtain ⟨V, hVβ, hVK⟩ := exists_mem_of_mem_etaSet hΩ hβ' hK ⟨hU, hUS'⟩ (hUR.trans hR.1)
  exact hβK V hVβ hVK

theorem eta_inf_mem_of_cyc66 (hΩ : HypOmegaGen Ω)
    (hC : Cyc66 Ω) {S : Sylow 2 G} {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
    (hηS : ∀ V ∈ η, V ≤ (S : Subgroup G)) {K : Subgroup G} (hK : K ∈ Ω)
    (h2 : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) : K ⊓ (⨆ V ∈ η, V) ∈ η := by
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  obtain ⟨habel, hUW⟩ := eta_abelian_of_cyc66 hΩ hC hS₁ hinv
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  obtain ⟨U, hU, hUK⟩ := exists_mem_UinS_of_two_lt hΩ hC S hK h2
  obtain ⟨V₀, hV₀η, hV₀K⟩ := exists_mem_of_mem_etaSet hΩ hηS' hK hU hUK
  have hV₀U : V₀ ∈ USet Ω := (hηS'.1 hV₀η).1
  set W : Subgroup G := ⨆ V ∈ η, V with hW
  have hWS : W ≤ (S : Subgroup G) := iSup₂_le fun V hV => hηS V hV
  have hV₀W : V₀ ≤ W := le_iSup₂_of_le V₀ hV₀η le_rfl
  have hX2 : IsPGroup 2 ↥(K ⊓ W) := (S.isPGroup'.to_le hWS).to_inf_right
  obtain ⟨R₀, -, J, hJ, hR₀J, hV₀R₀, -, hR₀card, -⟩ := exists_data_of_mem_USet hΩ hV₀U
  have hJK : J = K := eq_of_mem_USet hΩ hV₀U hJ hK (hV₀R₀.trans hR₀J.1) hV₀K
  have hR₀K : IsSylow2In R₀ K := hJK ▸ hR₀J
  obtain ⟨R₁, hR₁, hXR₁⟩ := IsSylow2In.exists_ge hX2 (inf_le_left : K ⊓ W ≤ K)
  have hR₁card : Nat.card R₁ = 2 * Nat.card V₀ := by rw [← hR₀card, hR₁.natCard_eq hR₀K]
  have hV₀X : V₀ ≤ K ⊓ W := le_inf hV₀K hV₀W
  rcases eq_or_eq_of_natCard_eq_two_mul hV₀X hXR₁ hR₁card with hX | hX
  · rw [hX]
    exact hV₀η
  · exfalso
    have hquat := isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR₁)
    obtain ⟨x, hx, y, hy, hxy⟩ := hquat.exists_not_commute
    rw [← hX] at hx hy
    exact hxy (habel x hx.2 y hy.2)

end Finite

theorem l6_11Gen : L6_11Gen := by
  intro G _ _ Ω hΩ S η hη hηS K hK h2
  exact eta_inf_mem_of_cyc66 hΩ (cyc66 hΩ) hη hηS hK h2


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
