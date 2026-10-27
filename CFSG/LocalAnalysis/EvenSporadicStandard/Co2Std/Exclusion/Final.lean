module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.LemmaJ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.FusionW
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.PropX
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.NormalizerTransfer

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G} {W W₁ W₂ : Subgroup G}

private theorem WHyp.kGroup_xw (h : WHyp G L A T z t W W₁ W₂) :
    KCore.KGroupNonab CFSG.Blueprint.Catalog ↥(XW W) := by
  haveI : IsSimpleGroup G := h.hyp.std.simple
  have hNne : normalizer (W : Set G) ≠ ⊤ := by
    rintro htop
    haveI hWnorm : W.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hWne : W ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card W = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [h.e3.card] at hcard
      norm_num at hcard
    have hWtop : W = ⊤ := (Subgroup.Normal.eq_bot_or_eq_top W).resolve_left hWne
    obtain ⟨a, b, hab⟩ := h.hyp.std.nonabelian
    haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
    refine hab (Subgroup.mul_comm_of_mem_isMulCommutative (H := W) ?_ ?_)
    · rw [hWtop]; exact Subgroup.mem_top a
    · rw [hWtop]; exact Subgroup.mem_top b
  exact (KCore.KProperNonab.kGroupNonab CFSG.SectionRank.catalog_isoInvariant
    h.hyp.std.kProper (normalizer (W : Set G)) hNne).of_surjective
    CFSG.SectionRank.catalog_isoInvariant (toXW W) (toXW_surjective W)

private theorem WHyp.toXW_eq_one_of_mem (h : WHyp G L A T z t W W₁ W₂) {w : G} (hw : w ∈ W) :
    toXW W ⟨w, Subgroup.le_normalizer hw⟩ = 1 := by
  haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
  have hker : (⟨w, Subgroup.le_normalizer hw⟩ :
      ↥(normalizer (W : Set G))) ∈ W.normalizerMonoidHom.ker := by
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mul_comm_of_mem_isMulCommutative (H := W) hv hw
  have h1 : W.normalizerMonoidHom ⟨w, Subgroup.le_normalizer hw⟩ = 1 :=
    MonoidHom.mem_ker.mp hker
  exact Subtype.ext h1

private theorem WHyp.exists_index_two_pullback (h : WHyp G L A T z t W W₁ W₂)
    {X₀ : Subgroup ↥(XW W)} (hX₀ : X₀.Normal) (hX₀i : X₀.index = 2)
    (hzX₀ : toXW W ⟨z, h.z_mem_normalizer⟩ ∉ X₀) :
    ∃ N₀ : Subgroup G, (N₀.subgroupOf (normalizer (W : Set G))).Normal ∧
      N₀.relIndex (normalizer (W : Set G)) = 2 ∧ z ∉ N₀ := by
  set N₀ : Subgroup G := (X₀.comap (toXW W)).map (normalizer (W : Set G)).subtype with hN₀
  have hsub : N₀.subgroupOf (normalizer (W : Set G)) = X₀.comap (toXW W) := by
    rw [hN₀]
    exact Subgroup.comap_map_eq_self_of_injective (normalizer (W : Set G)).subtype_injective _
  refine ⟨N₀, ?_, ?_, ?_⟩
  · rw [hsub]
    exact hX₀.comap (toXW W)
  · change (N₀.subgroupOf (normalizer (W : Set G))).index = 2
    rw [hsub, Subgroup.index_comap_of_surjective X₀ (toXW_surjective W), hX₀i]
  · intro hz
    have hz' : (⟨z, h.z_mem_normalizer⟩ : ↥(normalizer (W : Set G))) ∈
        N₀.subgroupOf (normalizer (W : Set G)) := Subgroup.mem_subgroupOf.mpr hz
    rw [hsub] at hz'
    exact hzX₀ (Subgroup.mem_comap.mp hz')

private theorem WHyp.exists_sylow_data (h : WHyp G L A T z t W W₁ W₂)
    {Q : Subgroup ↥(XW W)} {P : Sylow 2 ↥(XW W)}
    (hzP : toXW W ⟨z, h.z_mem_normalizer⟩ ∈ P)
    (hgood : ∀ x ∈ P, XGood (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W) x) :
    ∃ (S : Subgroup G) (hSN : S ≤ normalizer (W : Set G)),
      IsPGroup 2 S ∧ z ∈ S ∧ W ≤ S ∧
      (∀ R : Subgroup G, IsPGroup 2 R → S ≤ R → R ≤ normalizer (W : Set G) → R = S) ∧
      (∀ s (hs : s ∈ S), XGood (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W)
        (toXW W ⟨s, hSN hs⟩)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G :=
    ((P : Subgroup ↥(XW W)).comap (toXW W)).map (normalizer (W : Set G)).subtype with hHdef
  have hHN : H ≤ normalizer (W : Set G) := by
    rw [hHdef]
    exact Subgroup.map_subtype_le _
  have hHsub : H.subgroupOf (normalizer (W : Set G)) =
      (P : Subgroup ↥(XW W)).comap (toXW W) := by
    rw [hHdef]
    exact Subgroup.comap_map_eq_self_of_injective (normalizer (W : Set G)).subtype_injective _
  have hzH : z ∈ H := by
    rw [hHdef]
    exact Subgroup.mem_map.mpr
      ⟨⟨z, h.z_mem_normalizer⟩, Subgroup.mem_comap.mpr hzP, rfl⟩
  have hWH : W ≤ H := by
    intro w hw
    rw [hHdef]
    refine Subgroup.mem_map.mpr ⟨⟨w, Subgroup.le_normalizer hw⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, h.toXW_eq_one_of_mem hw]
    exact P.one_mem
  have hWz2 : IsPGroup 2 (W ⊔ zpowers z : Subgroup G) := by
    refine IsPGroup.of_card (n := 21) ?_
    rw [card_sup_zpowers_of_mem_normalizer h.z_mem_normalizer h.hyp.z_sq h.e3.z_not_mem,
      h.e3.card]
    norm_num
  have hWzH : W ⊔ zpowers z ≤ H := by
    apply sup_le
    · exact hWH
    · exact Subgroup.zpowers_le.mpr hzH
  obtain ⟨S', hS'le⟩ := (hWz2.comap_subtype (K := H)).exists_le_sylow
  set S : Subgroup G := (S' : Subgroup ↥H).map H.subtype with hSdef
  have hSH : S ≤ H := by
    rw [hSdef]
    exact Subgroup.map_subtype_le _
  have hSN : S ≤ normalizer (W : Set G) := hSH.trans hHN
  have hS2 : IsPGroup 2 S := by
    rw [hSdef]
    exact S'.isPGroup'.map H.subtype
  have hzS : z ∈ S := by
    rw [hSdef]
    exact Subgroup.mem_map.mpr
      ⟨⟨z, hWzH (mem_sup_right (mem_zpowers z))⟩,
        hS'le (Subgroup.mem_subgroupOf.mpr (mem_sup_right (mem_zpowers z))), rfl⟩
  have hWS : W ≤ S := by
    intro w hw
    rw [hSdef]
    exact Subgroup.mem_map.mpr
      ⟨⟨w, hWzH (mem_sup_left hw)⟩,
        hS'le (Subgroup.mem_subgroupOf.mpr (mem_sup_left hw)), rfl⟩
  set φ : ↥H →* ↥(XW W) := (toXW W).comp (Subgroup.inclusion hHN) with hφdef
  have hφ_range : φ.range = (P : Subgroup ↥(XW W)) := by
    ext x
    constructor
    · rintro ⟨hx, rfl⟩
      have hxH : Subgroup.inclusion hHN hx ∈ (P : Subgroup ↥(XW W)).comap (toXW W) := by
        rw [← hHsub]
        exact Subgroup.mem_subgroupOf.mpr hx.2
      exact Subgroup.mem_comap.mp hxH
    · intro hx
      obtain ⟨n, hn⟩ := toXW_surjective W x
      have hnH : (n : G) ∈ H := by
        rw [hHdef]
        exact Subgroup.mem_map.mpr ⟨n, by rw [Subgroup.mem_comap]; rwa [hn], rfl⟩
      refine ⟨⟨(n : G), hnH⟩, ?_⟩
      show toXW W (Subgroup.inclusion hHN ⟨(n : G), hnH⟩) = x
      rw [show Subgroup.inclusion hHN ⟨(n : G), hnH⟩ = n from Subtype.ext rfl]
      exact hn
  set φP : ↥H →* ↥P := φ.codRestrict P (fun hx => by
    show φ hx ∈ (P : Subgroup ↥(XW W))
    rw [← hφ_range]
    exact MonoidHom.mem_range.mpr ⟨hx, rfl⟩) with hφPdef
  have hφP_surj : Function.Surjective φP := by
    intro p
    have hp : (p : ↥(XW W)) ∈ φ.range := by
      rw [hφ_range]
      exact p.2
    obtain ⟨hx, hhx⟩ := MonoidHom.mem_range.mp hp
    exact ⟨hx, Subtype.ext hhx⟩
  have hS'top : ((S'.mapSurjective hφP_surj) : Subgroup ↥P) = ⊤ := by
    have h := (S'.mapSurjective hφP_surj).is_maximal' (Q := ⊤)
      (P.isPGroup'.to_subgroup ⊤) le_top
    exact h.symm
  have hS'φ : (S' : Subgroup ↥H).map φ = (P : Subgroup ↥(XW W)) := by
    have htop : (S' : Subgroup ↥H).map φP = ⊤ := by
      rw [← Sylow.coe_mapSurjective (P := S') hφP_surj]
      exact hS'top
    calc (S' : Subgroup ↥H).map φ =
          ((S' : Subgroup ↥H).map φP).map (P : Subgroup ↥(XW W)).subtype := by
          rw [Subgroup.map_map]
          rfl
      _ = (⊤ : Subgroup ↥P).map (P : Subgroup ↥(XW W)).subtype := by rw [htop]
      _ = (P : Subgroup ↥(XW W)) := by
          rw [← Subgroup.subgroupOf_self (H := (P : Subgroup ↥(XW W)))]
          exact Subgroup.map_subgroupOf_eq_of_le le_rfl
  have hSsub : S.subgroupOf (normalizer (W : Set G)) =
      (S' : Subgroup ↥H).map (Subgroup.inclusion hHN) := by
    ext n
    constructor
    · intro hn
      have hnS : (n : G) ∈ S := Subgroup.mem_subgroupOf.mp hn
      rw [hSdef] at hnS
      obtain ⟨hx, hhx, hhe⟩ := Subgroup.mem_map.mp hnS
      exact Subgroup.mem_map.mpr ⟨hx, hhx, Subtype.ext hhe⟩
    · rintro ⟨hx, hhx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by
        rw [hSdef]
        exact Subgroup.mem_map.mpr ⟨hx, hhx, rfl⟩)
  have hSπ : (S.subgroupOf (normalizer (W : Set G))).map (toXW W) =
      (P : Subgroup ↥(XW W)) := by
    rw [hSsub, Subgroup.map_map]
    exact hS'φ
  have hSmax : ∀ R : Subgroup G, IsPGroup 2 R → S ≤ R →
      R ≤ normalizer (W : Set G) → R = S := by
    intro R hR2 hSR hRN
    have hπR : (R.subgroupOf (normalizer (W : Set G))).map (toXW W) =
        (P : Subgroup ↥(XW W)) := by
      refine P.is_maximal' (Q := (R.subgroupOf (normalizer (W : Set G))).map (toXW W))
        (hR2.comap_subtype.map (toXW W)) ?_
      rw [← hSπ]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono (normalizer (W : Set G)) hSR)
    have hRH : R ≤ H := by
      intro r hr
      rw [hHdef]
      refine Subgroup.mem_map.mpr ⟨⟨r, hRN hr⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have hmem : toXW W ⟨r, hRN hr⟩ ∈
          (R.subgroupOf (normalizer (W : Set G))).map (toXW W) :=
        Subgroup.mem_map.mpr ⟨⟨r, hRN hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
      rwa [hπR] at hmem
    have hRsubH : (R.subgroupOf H).map H.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRH
    have hle : (S' : Subgroup ↥H) ≤ R.subgroupOf H := by
      intro hx hhx
      rw [Subgroup.mem_subgroupOf]
      exact hSR (by rw [hSdef]; exact Subgroup.mem_map.mpr ⟨hx, hhx, rfl⟩)
    have heq : R.subgroupOf H = (S' : Subgroup ↥H) :=
      S'.is_maximal' (hR2.comap_subtype) hle
    rw [← hRsubH, hSdef, heq]
  refine ⟨S, hSN, hS2, hzS, hWS, hSmax, ?_⟩
  intro s hs
  have hmem : toXW W ⟨s, hSN hs⟩ ∈
      (S.subgroupOf (normalizer (W : Set G))).map (toXW W) :=
    Subgroup.mem_map.mpr ⟨⟨s, hSN hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  rw [hSπ] at hmem
  exact hgood _ hmem

theorem WHyp.false (h : WHyp G L A T z t W W₁ W₂) (hKD : KDM22) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, Q₁, t₁, hx⟩ := h.exists_xHyp
  obtain ⟨⟨X₀, hX₀, hX₀i, hzX₀⟩, P, hzP, hgood⟩ := hx.concl hKD h.kGroup_xw
  obtain ⟨N₀, hN₀norm, hN₀idx, hzN₀⟩ := h.exists_index_two_pullback hX₀ hX₀i hzX₀
  obtain ⟨S, hSN, hS2, hzS, hWS, hSmax, hgood'⟩ := h.exists_sylow_data hzP hgood
  haveI : IsSimpleGroup G := h.hyp.std.simple
  have hz1 : z ≠ 1 := by
    intro hz1
    exact h.e3.z_not_mem (by rw [hz1]; exact W.one_mem)
  have hzord : orderOf z = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact h.hyp.z_sq) hz1
  exact CFSG.EvenSporadicStandard.false_of_index_two_of_controls_fusion
    (N := normalizer (W : Set G)) (N₀ := N₀) (S := S) (z := z)
    h.hyp.std.nonabelian hzord hN₀norm hN₀idx hzN₀ hSN hS2 hSmax hzS
    (h.normalizer_le_of_xGood hx hS2 hWS hSN hgood')
    (fun u hu hconj => h.exists_conj_of_isConj hu hconj)

theorem Hyp.false (h : Hyp G L A T z t) (hKD : KDM22) : False := by
  obtain ⟨W, W₁, W₂, hw⟩ := h.exists_wHyp
  exact hw.false hKD

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
