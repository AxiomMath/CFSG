module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G]

theorem map_conjClosure {G' : Type*} [Group G'] (f : G →* G') (Y E : Subgroup G) :
    (conjClosure Y E).map f = conjClosure (Y.map f) (E.map f) := by
  rw [conjClosure_eq_iSup, conjClosure_eq_iSup, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun e => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun he => ?_
    rw [UnbalancedLayer.map_conjugate]
    exact le_iSup₂_of_le (f e) (mem_map_of_mem f he) le_rfl
  · refine iSup₂_le fun e' he' => ?_
    obtain ⟨e, he, rfl⟩ := mem_map.mp he'
    rw [← UnbalancedLayer.map_conjugate]
    exact le_iSup_of_le e (by rw [Subgroup.map_iSup]; exact le_iSup_of_le he le_rfl)

theorem map_oddResidualIn {G' : Type*} [Group G'] (f : G →* G') (hf : Function.Injective f)
    (Y : Subgroup G) : (oddResidualIn Y).map f = oddResidualIn (Y.map f) := by
  unfold oddResidualIn
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, mem_map]
  constructor
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, k, by rw [orderOf_injective f hf y, hk]⟩
  · rintro ⟨⟨y, hy, rfl⟩, k, hk⟩
    exact ⟨y, ⟨hy, k, by rw [← orderOf_injective f hf y, hk]⟩, rfl⟩

variable [Finite G]

theorem foote_lemma_2_1_iv_subgroup {H : Subgroup G} {a : G} (haH : a ∈ H)
    (ha : orderOf a = 2) {K : Subgroup G} (hKC : K ≤ H ⊓ centralizer ({a} : Set G))
    (hK : IsPComponent 2 (K.subgroupOf (H ⊓ centralizer ({a} : Set G)))) :
    ∃ B : Subgroup G, B ≤ H ∧ IsPComponent 2 (B.subgroupOf H) ∧ K ≤ B ⊔ conjugate B a ∧
      conjClosure K (twoLayerIn H) = B ⊔ conjugate B a ∧
      ((conjugate B a = B ∧ B = oddResidualIn (K ⊔ oddCoreIn H) ∧
          Nonempty (K ⧸ pPrimeCore 2 K ≃* B ⧸ pPrimeCore 2 B)) ∨
        (conjugate B a = B ∧ K ⊔ oddCoreIn B < B ∧
          IsEmpty (K ⧸ Open.fusionZStar K ≃* B ⧸ Open.fusionZStar B)) ∨
        (conjugate B a ≠ B ∧
          K = twoLayerIn ((B ⊔ conjugate B a) ⊓ centralizer ({a} : Set G)) ∧
          (pPrimeCore 2 K).index ≤ (pPrimeCore 2 B).index)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := hKC.trans inf_le_left
  set a' : H := ⟨a, haH⟩ with ha'
  have ha'2 : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena : centralizer ({a'} : Set H) = (H ⊓ centralizer ({a} : Set G)).subgroupOf H := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨y.2, congrArg Subtype.val h⟩, fun h => Subtype.ext h.2⟩
  set K' := K.subgroupOf H with hK'
  have hK'C : K' ≤ centralizer ({a'} : Set H) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hKC (mem_subgroupOf.mp hy))
  have hK'pc : IsPComponent 2 (K'.subgroupOf (centralizer ({a'} : Set H))) := by
    rw [hcena, isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two]
    exact hK
  obtain ⟨B', hB', hKB', hcl', hcase⟩ := foote_lemma_2_1_iv ha'2 hK'C hK'pc
  set B := B'.map H.subtype with hB
  have hBH : B ≤ H := map_subtype_le _
  have hB'eq : B' = B.subgroupOf H := (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hBpc : IsPComponent 2 (B.subgroupOf H) := hB'eq ▸ hB'
  have hBaH : conjugate B a ≤ H := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 := mul_mem (mul_mem (inv_mem haH) (hBH hx)) haH
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h1
  have hconj' : conjugate B' a' = (conjugate B a).subgroupOf H := by
    rw [hB'eq, conjugate_subgroupOf_eq]
  have hmapc : (conjugate B' a').map H.subtype = conjugate B a := by
    rw [UnbalancedLayer.map_conjugate]
    rfl
  have hsup' : B' ⊔ conjugate B' a' = (B ⊔ conjugate B a).subgroupOf H := by
    rw [hconj', hB'eq, subgroupOf_sup hBH hBaH]
  have hmapsup : (B' ⊔ conjugate B' a').map H.subtype = B ⊔ conjugate B a := by
    rw [Subgroup.map_sup, hmapc]
  have hKmap : K'.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hKB : K ≤ B ⊔ conjugate B a := by
    rw [← hKmap, ← hmapsup]
    exact map_mono hKB'
  have hcl : conjClosure K (twoLayerIn H) = B ⊔ conjugate B a := by
    have hL : twoLayerIn H = (pLayer ↥H 2).map H.subtype := rfl
    rw [hL, ← hmapsup, ← hcl', map_conjClosure, hKmap]
  let eK : K' ≃* K := subgroupOfEquivOfLe hKH
  let eB : B' ≃* B := B'.equivMapOfInjective H.subtype H.subtype_injective
  have hB'inj : ∀ {X Y : Subgroup H}, X.map H.subtype = Y.map H.subtype → X = Y :=
    fun h => map_injective H.subtype_injective h
  refine ⟨B, hBH, hBpc, hKB, hcl, ?_⟩
  rcases hcase with ⟨hBa, hBres, ⟨e⟩⟩ | ⟨hBa, hlt, hiso⟩ | ⟨hne, hKlay, hidx⟩
  ·
    left
    have hBa' : conjugate B a = B := by rw [← hmapc, hBa]
    refine ⟨hBa', ?_, ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eK).symm.trans
      (e.trans (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eB))⟩⟩
    have h1 := congrArg (Subgroup.map H.subtype) hBres
    rw [map_oddResidualIn _ H.subtype_injective, Subgroup.map_sup, hKmap] at h1
    exact h1
  ·
    right; left
    have hBa' : conjugate B a = B := by rw [← hmapc, hBa]
    have hOB : (oddCoreIn B').map H.subtype = oddCoreIn B := by
      rw [hB'eq]
      exact pPrimeCore_map_subgroupOf 2 B H hBH
    refine ⟨hBa', ?_, ⟨fun e' => ?_⟩⟩
    · have h1 := (map_lt_map_iff_of_injective H.subtype_injective).mpr hlt
      rw [Subgroup.map_sup, hKmap, hOB] at h1
      exact h1
    · obtain ⟨eK'⟩ := nonempty_quotient_fusionZStar_equiv eK
      obtain ⟨eB'⟩ := nonempty_quotient_fusionZStar_equiv eB
      exact hiso.false (eK'.trans (e'.trans eB'.symm))
  ·
    right; right
    refine ⟨fun h => hne (hB'inj (by rw [hmapc, h])), ?_, ?_⟩
    · have hY : B ⊔ conjugate B a ≤ H := sup_le hBH hBaH
      have h1 := UnbalancingLocal.Correspondence.gsFixedLayer_subgroupOf hY haH
      apply UGSChain.eq_of_subgroupOf_eq hKH
        ((UnbalancedGS.gsFixedLayer_le_inf _ a).trans (inf_le_left.trans hY))
      rw [show K.subgroupOf H = K' from rfl, hKlay, hsup']
      exact h1.symm
    · have h1 := UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr (p := 2) eK
      have h2 := UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr (p := 2) eB
      rw [index_eq_card, index_eq_card] at hidx ⊢
      rw [← h1, ← h2]
      exact hidx

end CFSG.ComponentClassification.FooteLit
