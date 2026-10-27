module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Stage
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Transport
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Generation
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

namespace ZLayerData3

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X} {z : X}

theorem le_core_of_beta (h : ZLayerData3 X P z) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZ : center K ≠ ⊥) (hPN : (P : Subgroup X) ≤ normalizer (K : Set X))
    (hΩ : ∀ c ∈ (P : Subgroup X) ⊓ centralizer (K : Set X), orderOf c = 3 → c ∈ zpowers z)
    {D : Subgroup X} (hDP : D ≤ (P : Subgroup X)) (hD3 : ∀ x ∈ D, x ^ 3 = 1) (hzD : z ∈ D)
    (hDn : ¬ (P : Subgroup X) ≤ normalizer (D : Set X))
    (hList : KFactAlphaListM3) (hSmall : KFactAlphaSmallAut3Card)
    (hOn : KFactAlphaOnan3Comm) (hLift : KFactSL3LiftGen) :
    K ≤ rankThreeAschCore 2 3 (P : Subgroup X) := by
  obtain ⟨hzK, hzcK, -⟩ := h.component_center hK hZ
  have hz1 : z ≠ 1 := fun e => by
    have := h.ord
    rw [e, orderOf_one] at this
    omega
  have hzP : ∀ g ∈ (P : Subgroup X), z * g = g * z := fun g hg =>
    (mem_centralizer_iff.1 h.cent g hg).symm
  let Y : Subgroup X := normalizer (K : Set X) ⊓ centralizer ({z} : Set X)
  have hYN : Y ≤ normalizer (K : Set X) := inf_le_left
  have hKY : K ≤ Y := fun k hk =>
    ⟨le_normalizer hk, mem_centralizer_singleton_iff.2 (hzcK k hk).symm⟩
  have hPY : (P : Subgroup X) ≤ Y := fun g hg =>
    ⟨hPN hg, mem_centralizer_singleton_iff.2 (hzP g hg).symm⟩
  have hzY : z ∈ Y := hKY hzK
  have : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hYN
  let R : Sylow 3 ↥Y := P.subtype hPY
  have hR : (R : Subgroup ↥Y) = (P : Subgroup X).subgroupOf Y := Sylow.coe_subtype P hPY
  let z' : ↥Y := ⟨z, hzY⟩
  have hK' : IsComponentOf (K.subgroupOf Y) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.of_overgroup hK hKY
  have hcatY : CFSG.AGLEmbedding.CatalogSimpleSections ↥Y := h.cat.subgroup Y
  have hprank : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank 3 Nat.prime_three P).symm.trans
      h.prank
  have hz'3 : orderOf z' = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact h.ord
  have hΩ' : ∀ c ∈ (R : Subgroup ↥Y) ⊓ centralizer ((K.subgroupOf Y : Subgroup ↥Y) : Set ↥Y),
      orderOf c = 3 → c ∈ zpowers z' := by
    intro c hc hc3
    have hcP : (c : X) ∈ (P : Subgroup X) := by
      have := hc.1
      rw [hR] at this
      exact mem_subgroupOf.1 this
    have hcK : (c : X) ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val (mem_centralizer_iff.1 hc.2 ⟨k, hKY hk⟩ (mem_subgroupOf.2 hk))
    have hcz : (c : X) ∈ zpowers z :=
      hΩ (c : X) ⟨hcP, hcK⟩ ((Subgroup.orderOf_coe c).trans hc3)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hcz
    exact mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
  have hR3 : CFSG.Open.pRank 3 (R : Subgroup ↥Y) = 3 := by
    have h1 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
      Y.subtype Y.subtype_injective ((P : Subgroup X).subgroupOf Y)
    rw [map_subgroupOf_eq_of_le hPY] at h1
    rw [hR]
    exact h1.symm.trans h.prank
  have hDR : D.subgroupOf Y ≤ (R : Subgroup ↥Y) := by
    intro x hx
    rw [hR]
    exact mem_subgroupOf.2 (hDP (mem_subgroupOf.1 hx))
  have hD3' : ∀ x ∈ D.subgroupOf Y, x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by simpa using hD3 x (mem_subgroupOf.1 hx))
  have hDn' : ¬ (R : Subgroup ↥Y) ≤ normalizer ((D.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [hR]
    exact not_le_normalizer_subgroupOf hPY hDP hDn
  obtain ⟨A, hAR, hA, hA3, hgen⟩ := exists_generation_of_beta_data R (K.subgroupOf Y)
    (z := z') hK'.2.2 (cfsgIsKGroup_of_catalogSimpleSections (hcatY.subgroup _))
    ((twoLocalOddRank_subgroupOf_le hKY).trans h.rank)
    (hcatY.isCatalogGroup_center_quotient hK')
    (center_subgroupOf_ne_bot hKY hzK hzcK hz1)
    (isPGroup_center_subgroupOf hKY (h.isPGroup_center hK))
    (isCyclic_center_subgroupOf hKY (h.isCyclic_center hK))
    ((pRank_top_subgroupOf_le hKY).trans hprank.le)
    (mem_subgroupOf.2 hzK)
    (fun k hk => Subtype.ext (hzcK k (mem_subgroupOf.1 hk)))
    (mem_center_iff.2 fun g => Subtype.ext (mem_centralizer_singleton_iff.1 g.2.2))
    hz'3 hΩ' hR3 hDR hD3' (mem_subgroupOf.2 hzD) hDn' hList hSmall hOn hLift
  exact le_rankThreeAschCore_of_generation hKY hPY h.ord h.memP hzP hzcK
    (hAR.trans hR.le) hA hA3 hgen

end ZLayerData3

end CFSG.LocalAnalysis.RankThreeTheoremC
