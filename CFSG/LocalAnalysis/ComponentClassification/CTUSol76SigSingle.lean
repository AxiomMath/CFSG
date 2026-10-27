module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigMain

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

omit [Finite G] in
theorem sup_inf_le_sup_inf_of_le {X A M : Subgroup G} (hXM : X ≤ M)
    (hXA : X ≤ normalizer (A : Set G)) : (X ⊔ A) ⊓ M ≤ X ⊔ (A ⊓ M) := by
  rintro y ⟨hy, hyM⟩
  rw [sup_comm] at hy
  obtain ⟨a, ha, k, hk, rfl⟩ := exists_mul_of_mem_sup_normalizer hXA hy
  have haM : a ∈ M := by
    have e : a = a * k * k⁻¹ := by group
    rw [e]
    exact M.mul_mem hyM (M.inv_mem (hXM hk))
  exact mul_mem (mem_sup_right ⟨ha, haM⟩) (mem_sup_left hk)

theorem exists_twoComponent_sup_eq_of_single (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {H M : Subgroup G} (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H)
    (hM : IsTwoComponentIn M H) (hall : ∀ K ∈ kStarComponents N, K ≤ M) {K K' : Subgroup G}
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {x : G}
    (hxK : x ∈ K) (hx2 : orderOf x = 2) :
    ∃ P : Subgroup G, IsTwoComponentIn P (M ⊓ centralizer ({x} : Set G)) ∧
      P ⊔ oddCoreIn (M ⊓ centralizer ({x} : Set G)) =
        twoLayerIn (K' ⊓ centralizer ({x} : Set G)) ⊔
          oddCoreIn (M ⊓ centralizer ({x} : Set G)) := by
  classical
  set C := centralizer ({x} : Set G) with hC
  obtain ⟨P, hP, B', hB', hPB', hK'B', hPH⟩ :=
    exists_pump_le hq hR1 hG hN hKH hLH hK' hK hne.symm hxK hx2
  have hB'M : B' = M := eq_of_le_of_le_isTwoComponentIn hB' hM hK'B' (hall K' hK')
    (UnbalancedCorr.commutator_eq_of_isPComponent hK'.1.1 hK'.1.2)
    (exists_orderOf_eq_two_of_mem_solomonKStar hK'.2)
  have hPM : P ≤ M := hB'M ▸ hPB'
  have hPC : P ≤ C := hPH.1.trans inf_le_right
  have hPMC : IsTwoComponentIn P (M ⊓ C) :=
    isTwoComponentIn_of_le hPH (le_inf hPM hPC) (inf_le_inf_right _ hM.1)
  refine ⟨P, hPMC, ?_⟩
  obtain ⟨P', hP', hsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK' hK hne.symm hxK hx2
  have h1 := ncard_pumpSet_eq_one hq hR1 hG hN hK' hK hne.symm hxK hx2
  obtain ⟨P₀, hP₀⟩ := Set.ncard_eq_one.mp h1
  have hPP' : P' = P := by
    have e1 : P' ∈ ({P₀} : Set (Subgroup G)) := hP₀ ▸ hP'
    have e2 : P ∈ ({P₀} : Set (Subgroup G)) := hP₀ ▸ hP
    rw [Set.mem_singleton_iff] at e1 e2
    rw [e1, e2]
  rw [hPP'] at hsup
  set A := oddCoreIn (twoLayerIn C) with hA
  set O' := oddCoreIn (M ⊓ C) with hO'
  set Y := twoLayerIn (K' ⊓ C) with hY
  have hAC : A ≤ C := (map_subtype_le _).trans (map_subtype_le _)
  have hCA : C ≤ normalizer (A : Set G) := le_normalizer_oddCoreIn_twoLayerIn C
  have hAO : A ⊓ M ≤ O' := fun a ha =>
    inf_le_oddCoreIn (coprime_card_oddCoreIn _) (inf_le_right.trans hCA) ⟨ha.1, ha.2, hAC ha.1⟩
  have hx2' : x ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK hK' hne hxK
  obtain ⟨hY2, -, -, -, -⟩ := pump_facts hK' hx2' hx2
  have hYM : Y ≤ M := (hY2.1.trans inf_le_left).trans (hall K' hK')
  have hYC : Y ≤ C := hY2.1.trans inf_le_right
  have hPY : P ≤ Y ⊔ O' := by
    have h := le_inf (le_sup_left.trans (hsup.symm ▸ le_rfl : P ⊔ A ≤ Y ⊔ A)) hPM
    exact (h.trans (sup_inf_le_sup_inf_of_le hYM (hYC.trans hCA))).trans (sup_le_sup_left hAO _)
  have hYP : Y ≤ P ⊔ O' := by
    have h := le_inf (le_sup_left.trans (hsup ▸ le_rfl : Y ⊔ A ≤ P ⊔ A)) hYM
    exact (h.trans (sup_inf_le_sup_inf_of_le hPM (hPC.trans hCA))).trans (sup_le_sup_left hAO _)
  exact le_antisymm (sup_le hPY le_sup_right) (sup_le hYP le_sup_right)

@[expose] def SingleComponentCatalogFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G),
    IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) →
    Blueprint.Catalog ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) →
    ∀ K₁ K₂ : Subgroup G, K₁ ≤ M → K₂ ≤ M → ⁅K₁, K₁⁆ = K₁ → ⁅K₂, K₂⁆ = K₂ →
      IsQuasisimple (↥K₁ ⧸ pPrimeCore 2 ↥K₁) → IsQuasisimple (↥K₂ ⧸ pPrimeCore 2 ↥K₂) →
      2 ≤ CFSG.Open.pRank 2 K₁ → 2 ≤ CFSG.Open.pRank 2 K₂ →
      ⁅K₁, K₂⁆ ≤ oddCoreIn K₁ ⊓ oddCoreIn K₂ →
      (∀ x ∈ K₁, orderOf x = 2 → ∃ P : Subgroup G,
        IsTwoComponentIn P (M ⊓ centralizer ({x} : Set G)) ∧
        P ⊔ oddCoreIn (M ⊓ centralizer ({x} : Set G)) =
          twoLayerIn (K₂ ⊓ centralizer ({x} : Set G)) ⊔
            oddCoreIn (M ⊓ centralizer ({x} : Set G))) →
      (∀ y ∈ K₂, orderOf y = 2 → ∃ P : Subgroup G,
        IsTwoComponentIn P (M ⊓ centralizer ({y} : Set G)) ∧
        P ⊔ oddCoreIn (M ⊓ centralizer ({y} : Set G)) =
          twoLayerIn (K₁ ⊓ centralizer ({y} : Set G)) ⊔
            oddCoreIn (M ⊓ centralizer ({y} : Set G))) →
      False

theorem commutator_le_oddCoreIn_inf {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') :
    ⁅K, K'⁆ ≤ oddCoreIn K ⊓ oddCoreIn K' := by
  refine le_inf (commutator_le_oddCoreIn_of_le_coreActionKernel
    (le_coreActionKernel_of_ne hK hK' hne)) ?_
  rw [commutator_comm]
  exact commutator_le_oddCoreIn_of_le_coreActionKernel (le_coreActionKernel_of_ne hK' hK hne.symm)

theorem singleComponentExcludedFor_of_catalog (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hC : SingleComponentCatalogFor) :
    SingleComponentExcludedFor := by
  intro G _ _ hG N hN K K' V B hP hW hKH hLH M hM hall
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    isQuasisimple_quotient_of_isPComponent hM.1 hM.2
  have hMtop : M ≠ ⊤ := by
    intro htop
    have hHtop : normalizer (wGroup B V : Set G) = ⊤ := top_le_iff.mp (htop ▸ hM.1)
    have hnorm : (wGroup B V).Normal := normalizer_eq_top_iff.mp hHtop
    have : IsSimpleGroup G := hG.1
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact hW h
    · have hodd := (wGroup_spec_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK
        (by rw [hB8]; norm_num)).1
      rw [h, Subgroup.card_top] at hodd
      obtain ⟨b, -, hb2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK.2
      have h2 : 2 ∣ Nat.card G := hb2 ▸ orderOf_dvd_natCard b
      exact absurd (Nat.Coprime.eq_one_of_dvd hodd h2) (by norm_num)
  have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
  have hcat := QuasithinUnique.catalog_of_kProper_of_surjective hG.2.2 M hMtop _ hMq.2.2
    ((QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))).comp
      (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  exact hC G M hMq hcat K K' (hall K hK) (hall K' hK')
    (UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2)
    (UnbalancedCorr.commutator_eq_of_isPComponent hK'.1.1 hK'.1.2)
    (isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2)
    (isQuasisimple_quotient_of_isPComponent hK'.1.1 hK'.1.2)
    (two_le_pRank_of_mem_solomonKStar hK.2) (two_le_pRank_of_mem_solomonKStar hK'.2)
    (commutator_le_oddCoreIn_inf hK hK' hne)
    (fun x hx hx2 => exists_twoComponent_sup_eq_of_single hq hR1 hG hN hKH hLH hM hall hK hK' hne
      hx hx2)
    (fun y hy hy2 => exists_twoComponent_sup_eq_of_single hq hR1 hG hN hKH hLH hM hall hK' hK
      hne.symm hy hy2)

end CFSG.ComponentClassification.Sol76.Sig
