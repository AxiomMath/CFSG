module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.SylowNormalizerContainment
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalSylowIntersection

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_in_normalized_product (L A R : Subgroup G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    (L ⊔ A) ⊓ Subgroup.normalizer (R : Set G) =
      (L ⊓ Subgroup.normalizer (R : Set G)) ⊔ A := by
  apply le_antisymm _ (sup_le
    (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
    (le_inf le_sup_right hAR))
  intro x hx
  obtain ⟨l, hl, b, hb, heq⟩ := NormalizedProduct.coordinates L A hAL x hx.1
  have hlR : l ∈ Subgroup.normalizer (R : Set G) := by
    have hmem := (Subgroup.normalizer (R : Set G)).mul_mem hx.2
      ((Subgroup.normalizer (R : Set G)).inv_mem (hAR hb))
    rw [← heq, mul_inv_cancel_right] at hmem
    exact hmem
  rw [← heq]
  exact Subgroup.mul_mem_sup ⟨hl, hlR⟩ hb

theorem maximal_invariant_two_sylow_alternative (a : G) (ha : orderOf a = 2)
    (K L S : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (hL : IsComponentOf L ⊤) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hSL : S ≤ L) (htwo : IsPGroup 2 S)
    (haS : a ∈ Subgroup.normalizer (S : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G))
    (hmaximal : ∀ T : Subgroup G, T ≤ L → IsPGroup 2 T →
      a ∈ Subgroup.normalizer (T : Set G) → K ≤ Subgroup.normalizer (T : Set G) →
      S ≤ T → T = S) :
    K ≤ L ∨ ∃ P : Sylow 2 L,
      (P : Subgroup L).map L.subtype = S ∧ K ≤ Subgroup.centralizer (S : Set G) ∧
      ∃ Q : Sylow 2 ↥(L ⊔ Subgroup.zpowers a),
        (Q : Subgroup ↥(L ⊔ Subgroup.zpowers a)).map
          (L ⊔ Subgroup.zpowers a).subtype = S ⊔ Subgroup.zpowers a := by
  rcases maximal_invariant_two_normalizer_alternative a ha K L S hKC hK hL haL
      hSL htwo haS hKS hmaximal with hcontained | hcommutes
  · exact Or.inl hcontained
  right
  let A := Subgroup.zpowers a
  let H := L ⊔ A
  let R := S ⊔ A
  let RH := R.subgroupOf H
  let N := Subgroup.normalizer (RH : Set H)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr haL
  have haR : a ∈ Subgroup.normalizer (R : Set G) :=
    (Subgroup.inf_normalizer_le_normalizer_sup S A)
      ⟨haS, Subgroup.le_normalizer (Subgroup.mem_zpowers a)⟩
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr haR
  have hRH : R ≤ H := sup_le (hSL.trans le_sup_left) le_sup_right
  have hAtwo : IsPGroup 2 A := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, ha, pow_one])
  have hRtwo : IsPGroup 2 R := htwo.to_sup_of_normal_left' hAtwo
    (Subgroup.zpowers_le.mpr haS)
  have hcentralR : K ≤ Subgroup.centralizer (R : Set G) :=
    (invariant_two_component_in_common_centralizer a ha K S hKC hK htwo haS hKS).1
  have hcentralS : K ≤ Subgroup.centralizer (S : Set G) :=
    hcentralR.trans (Subgroup.centralizer_le (le_sup_left : S ≤ R))
  have hnormalizerK : H ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.centralizer (K : Set G) := by
    rw [normalizer_in_normalized_product L A R hAL hAR]
    exact sup_le
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes))
      ((le_sup_right : A ≤ R).trans (Subgroup.le_centralizer_iff.mp hcentralR))
  obtain ⟨QN, hRQN⟩ :=
    ((hRtwo.comap_subtype (K := H)).comap_subtype (K := N)).exists_le_sylow
  let QH := (QN : Subgroup N).map N.subtype
  let QG := QH.map H.subtype
  have hRHQH : RH ≤ QH := by
    have hmap := Subgroup.map_mono (f := N.subtype) hRQN
    change (RH.subgroupOf N).map N.subtype ≤ QH at hmap
    rwa [Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer : RH ≤ N)] at hmap
  have hRG : R ≤ QG := by
    have hmap := Subgroup.map_mono (f := H.subtype) hRHQH
    rw [Subgroup.map_subgroupOf_eq_of_le hRH] at hmap
    exact hmap
  have hQGN : QG ≤ H ⊓ Subgroup.normalizer (R : Set G) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    refine ⟨q.property, ?_⟩
    have hqN : q ∈ N := Subgroup.map_subtype_le _ hq
    change q ∈ Subgroup.normalizer (RH : Set H) at hqN
    rw [← Subgroup.subgroupOf_normalizer_eq hRH] at hqN
    exact hqN
  have hQGtwo : IsPGroup 2 QG := (QN.isPGroup'.map N.subtype).map H.subtype
  have hKQG : K ≤ Subgroup.centralizer (QG : Set G) :=
    Subgroup.le_centralizer_iff.mp (hQGN.trans hnormalizerK)
  have haQG : a ∈ QG := hRG ((le_sup_right : A ≤ R) (Subgroup.mem_zpowers a))
  have hintersection : QG ⊓ L = S := by
    apply hmaximal (QG ⊓ L) inf_le_right hQGtwo.to_inf_left
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer haQG, haL⟩
    · exact (hKQG.trans (Subgroup.centralizer_le (inf_le_left : QG ⊓ L ≤ QG))).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact le_inf ((le_sup_left : S ≤ R).trans hRG) hSL
  have hQGR : QG ≤ R := by
    intro x hx
    obtain ⟨l, hl, b, hb, heq⟩ := NormalizedProduct.coordinates L A hAL x (hQGN hx).1
    have hbQG : b ∈ QG := hRG ((le_sup_right : A ≤ R) hb)
    have hlQG : l ∈ QG := by
      have hmem := QG.mul_mem hx (QG.inv_mem hbQG)
      rw [← heq, mul_inv_cancel_right] at hmem
      exact hmem
    have hlS : l ∈ S := hintersection ▸ (show l ∈ QG ⊓ L from ⟨hlQG, hl⟩)
    rw [← heq]
    exact Subgroup.mul_mem_sup hlS hb
  have hQGeq : QG = R := le_antisymm hQGR hRG
  have hQHeq : QH = RH := by
    apply Subgroup.map_injective H.subtype_injective
    change QG = RH.map H.subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hRH]
    exact hQGeq
  obtain ⟨Q, hQ⟩ := SylowNormalizerContainment.ambient (G := H) N QN
    (by
      change Subgroup.normalizer (QH : Set H) ≤ N
      rw [hQHeq])
  have hQ' : (Q : Subgroup H) = QH := hQ
  have hQimage : (Q : Subgroup H).map H.subtype = R := by
    rw [hQ']
    exact hQGeq
  let LH := L.subgroupOf H
  let : LH.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer hAL)
  let QL := CFSG.RankThreeEvenClassification.Helpers.sylowNormalIntersection
    2 Nat.prime_two Q LH
  let e : LH ≃* L := Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  have heSurj : Function.Surjective e.toMonoidHom := by
    intro x
    obtain ⟨y, hy⟩ := e.surjective x
    exact ⟨y, hy⟩
  let P := QL.mapSurjective (f := e.toMonoidHom) heSurj
  have hPe : (P : Subgroup L) = (QL : Subgroup LH).map e.toMonoidHom :=
    Sylow.coe_mapSurjective heSurj QL
  have hPimage : (P : Subgroup L).map L.subtype = R ⊓ L := by
    rw [hPe, Subgroup.map_map]
    have hmaps : L.subtype.comp e.toMonoidHom = H.subtype.comp LH.subtype := by
      ext x
      rfl
    rw [hmaps, ← Subgroup.map_map,
      CFSG.RankThreeEvenClassification.Helpers.sylowNormalIntersection_coe,
      Subgroup.subgroupOf_map_subtype, Subgroup.map_inf _ _ _ H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : L ≤ H), hQimage]
  refine ⟨P, ?_, hcentralS, Q, hQimage⟩
  rw [hPimage, ← hQGeq]
  exact hintersection

end CFSG.ComponentClassification.AschbacherComponentInvolution
