module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalHull
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.Assembly

theorem map_subgroupOf_normal {H B : Type*} [Group H] [Group B] (f : H →* B) {D C : Subgroup H}
    (hDC : (D.subgroupOf C).Normal) (hle : D ≤ C) : ((D.map f).subgroupOf (C.map f)).Normal := by
  rw [normal_subgroupOf_iff (map_mono hle)]
  rintro _ _ ⟨d, hd, rfl⟩ ⟨c, hc, rfl⟩
  exact ⟨c * d * c⁻¹, (normal_subgroupOf_iff hle).mp hDC d c hd hc, by
    rw [map_mul, map_mul, map_inv]⟩

theorem map_rangeRestrict_eq_bot_iff {H B : Type*} [Group H] [Group B] (f : H →* B)
    (K : Subgroup H) : K.map f.rangeRestrict = ⊥ ↔ K.map f = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict]

variable {G : Type} [Group G] [Finite G]

theorem unbalancing_local_KProper_action_section {x y : G} (hy : orderOf y = 2)
    (hxy : x * y = y * x) (hxZ : x ∉ center G) {L : Subgroup G}
    (hLx : L ≤ centralizer ({x} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set G))))
    (hLy : ⁅L, zpowers y⁆ = L) (hLD : ⁅L, oddCentralizerMeet x y⁆ = L) :
    let D := oddCentralizerMeet x y
    let H := hull L y D
    let α := hullAction L y D hLy.le hLD.le
    let yH : H := ⟨y, mem_hull_elem L y D⟩
    H ≤ centralizer ({x} : Set G) ∧ centralizer ({x} : Set G) < ⊤ ∧ (L.subgroupOf H).Normal ∧
      (IsSimpleGroup (hullSection L H) ∧ ∃ s t : hullSection L H, s * t ≠ t * s) ∧
      (∀ (h : H) (l : L.subgroupOf H) (hl : h * l * h⁻¹ ∈ L.subgroupOf H),
        α h (l : hullSection L H) = ((⟨h * l * h⁻¹, hl⟩ : L.subgroupOf H) : hullSection L H)) ∧
      (MulAut.conj : hullSection L H →* MulAut (hullSection L H)).range ≤ α.range ∧
      generalizedFitting α.range =
        (MulAut.conj : hullSection L H →* MulAut (hullSection L H)).range.subgroupOf α.range ∧
      Nonempty ((MulAut.conj : hullSection L H →* MulAut (hullSection L H)).range.subgroupOf
        α.range ≃* hullSection L H) ∧
      orderOf (α yH) = 2 ∧
      (D.subgroupOf H).map α.rangeRestrict ≠ ⊥ ∧
      Odd (Nat.card ((D.subgroupOf H).map α.rangeRestrict)) ∧
      (D.subgroupOf H).map α.rangeRestrict ≤ centralizer {α.rangeRestrict yH} ∧
      (((D.subgroupOf H).map α.rangeRestrict).subgroupOf
        ((centralizer {yH}).map α.rangeRestrict)).Normal ∧
      (centralizer {yH}).map α.rangeRestrict ≤ centralizer {α.rangeRestrict yH} ∧
      (KProper InCatalog G →
        InCatalog (hullSection L H) ∧ CFSG.IsKGroup H ∧ CFSG.IsKGroup α.range) ∧
      (KProper Blueprint.Catalog G → Blueprint.Catalog (hullSection L H) ∧
        SectionRank.IsKGroupCat H ∧ SectionRank.IsKGroupCat α.range) := by
  intro D H α yH
  have hLH : L ≤ H := le_hull_left L y D
  have hDH : D ≤ H := le_hull_right L y D
  have hLn : (L.subgroupOf H).Normal := hull_normal hLy.le hLD.le
  have hHx : H ≤ centralizer ({x} : Set G) := hull_le_centralizer hxy hLx
  have hCx := centralizer_lt_top hxZ
  have hHtop : H ≠ ⊤ := (lt_of_le_of_lt hHx hCx).ne
  have hQ := hull_quasisimple hLx hL hLH
  obtain ⟨hS, -, -, hform, -, -, -, hInn, hF, hFe, hy1, hD1⟩ :=
    normal_quasisimple_section_automorphism_image (L.subgroupOf H) (pPrimeCore 2 (L.subgroupOf H))
      hQ
  have hαy1 : α yH ≠ 1 := hy1 yH (hull_commutator_elem hLy)
  have hy2 : yH ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαy : orderOf (α yH) = 2 := orderOf_eq_prime (by rw [← map_pow, hy2, map_one]) hαy1
  have hαD : (D.subgroupOf H).map α.rangeRestrict ≠ ⊥ := by
    rw [ne_eq, map_rangeRestrict_eq_bot_iff]
    exact hD1 (D.subgroupOf H) (hull_commutator_right hLD)
  have hαDodd : Odd (Nat.card ((D.subgroupOf H).map α.rangeRestrict)) := by
    have h1 : Nat.card ((D.subgroupOf H).map α.rangeRestrict) ∣ Nat.card D := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv]
      exact card_map_dvd _ _
    exact Nat.coprime_two_left.mp ((coprime_card_oddCentralizerMeet x y).coprime_dvd_right h1)
  have hDy : D.subgroupOf H ≤ centralizer {yH} := by
    intro d hd
    refine mem_centralizer_singleton.mpr (Subtype.ext ?_)
    exact mem_centralizer_singleton.mp (oddCentralizerMeet_le x y (mem_subgroupOf.mp hd))
  have hDn : ((D.subgroupOf H).subgroupOf (centralizer {yH})).Normal := by
    rw [normal_subgroupOf_iff hDy]
    intro d c hd hc
    rw [mem_subgroupOf] at hd ⊢
    have hcy : (c : G) ∈ centralizer ({y} : Set G) :=
      mem_centralizer_singleton.mpr (congrArg Subtype.val (mem_centralizer_singleton.mp hc))
    exact conj_mem_oddCentralizerMeet (hHx c.2) hcy hd
  have hcent : (centralizer {yH}).map α.rangeRestrict ≤ centralizer {α.rangeRestrict yH} := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton, ← map_mul, ← map_mul, mem_centralizer_singleton.mp hc]
  refine ⟨hHx, hCx, hLn, hS, hform, hInn, hF, hFe, hαy, hαD, hαDodd,
    (map_mono hDy).trans hcent, map_subgroupOf_normal _ hDn hDy, hcent, ?_, ?_⟩
  · intro hK
    have hKH : CFSG.IsKGroup H := CatalogueKProper.proper_subgroup_isKGroup hK H hHtop
    have hquot : CFSG.IsKGroup (H ⧸ α.ker) := kGroupOver_quotient inCatalog_of_mulEquiv hKH α.ker
    exact ⟨hKH (L.subgroupOf H) _ hS.1,
      hKH, (section_K_isomorphism (QuotientGroup.quotientKerEquivRange α).symm).1.mpr hquot⟩
  · intro hK
    have hKH : SectionRank.IsKGroupCat H :=
      kGroupOver_of_kProper SectionRank.catalog_of_mulEquiv catalog_of_abelian_simple hK H hHtop
    exact ⟨hKH (L.subgroupOf H) _ hS.1, hKH,
      (section_K_isomorphism (QuotientGroup.quotientKerEquivRange α).symm).2.mpr
        (hKH.quotient α.ker)⟩

end CFSG.ComponentClassification.UnbalancingLocal
