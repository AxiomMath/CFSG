module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

variable {G : Type*} [Group G]

theorem generator_central_mod_normal (B : Subgroup G) [B.Normal] (t : G)
    (hgenerated : B ⊔ Subgroup.zpowers t = ⊤) :
    QuotientGroup.mk' B t ∈ Subgroup.center (G ⧸ B) := by
  let q := QuotientGroup.mk' B
  have hcyclic : Subgroup.zpowers (q t) = ⊤ := by
    have hm := congrArg (Subgroup.map q) hgenerated
    simpa only [Subgroup.map_sup, q, QuotientGroup.map_mk'_self,
      MonoidHom.map_zpowers, bot_sup_eq,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective B)] using hm
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hg : g ∈ Subgroup.zpowers (q t) := hcyclic.symm ▸ Subgroup.mem_top g
  have hc : Subgroup.zpowers (q t) ≤ Subgroup.centralizer ({q t} : Set (G ⧸ B)) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hc hg)

theorem central_mod_normal_intersection (B J : Subgroup G) [B.Normal] [J.Normal]
    (t : G)
    (hB : QuotientGroup.mk' B t ∈ Subgroup.center (G ⧸ B))
    (hJ : QuotientGroup.mk' J t ∈ Subgroup.center (G ⧸ J)) :
    QuotientGroup.mk' (B ⊓ J) t ∈ Subgroup.center (G ⧸ (B ⊓ J)) := by
  apply Subgroup.mem_center_iff.mpr
  intro gq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (B ⊓ J) gq
  change (QuotientGroup.mk (g * t) : G ⧸ (B ⊓ J)) = QuotientGroup.mk (t * g)
  apply QuotientGroup.eq.mpr
  constructor
  · apply QuotientGroup.eq.mp
    have hc := Subgroup.mem_center_iff.mp hB (QuotientGroup.mk' B g)
    change (QuotientGroup.mk (g * t) : G ⧸ B) = QuotientGroup.mk (t * g) at hc
    exact hc
  · apply QuotientGroup.eq.mp
    have hc := Subgroup.mem_center_iff.mp hJ (QuotientGroup.mk' J g)
    change (QuotientGroup.mk (g * t) : G ⧸ J) = QuotientGroup.mk (t * g) at hc
    exact hc

theorem normalized_subgroup_odd_central_quotient [Finite G]
    (J X : Subgroup G) [J.Normal] (t : G)
    (hJodd : Odd (Nat.card J))
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (G ⧸ J)) :
    let L := X ⊔ Subgroup.zpowers t
    let B := X.subgroupOf L
    let A := B ⊓ J.subgroupOf L
    let tL : L := ⟨t, (show Subgroup.zpowers t ≤ L from le_sup_right)
      (Subgroup.mem_zpowers t)⟩
    ∃ (_hB : B.Normal) (hA : A.Normal), Odd (Nat.card A) ∧ A ≤ B ∧
      (B ⊔ Subgroup.zpowers tL = ⊤) ∧
      (letI : A.Normal := hA;
        QuotientGroup.mk' A tL ∈
          Subgroup.center (L ⧸ A)) := by
  let L := X ⊔ Subgroup.zpowers t
  let B := X.subgroupOf L
  let R := J.subgroupOf L
  have hXL : X ≤ L := le_sup_left
  have hLnorm : L ≤ Subgroup.normalizer (X : Set G) :=
    sup_le X.le_normalizer (Subgroup.zpowers_le.mpr hXnorm)
  let : B.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLnorm
  let : R.Normal := inferInstance
  let A := B ⊓ R
  let : A.Normal := inferInstance
  let tL : L := ⟨t, (show Subgroup.zpowers t ≤ L from le_sup_right)
    (Subgroup.mem_zpowers t)⟩
  have hBgen : B ⊔ Subgroup.zpowers tL = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXL,
      MonoidHom.map_zpowers, Subgroup.map_top, L.range_subtype]
    rfl
  have hRcentral : QuotientGroup.mk' R tL ∈ Subgroup.center (L ⧸ R) := by
    apply Subgroup.mem_center_iff.mpr
    intro gq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R gq
    change (QuotientGroup.mk (g * tL) : L ⧸ R) = QuotientGroup.mk (tL * g)
    apply QuotientGroup.eq.mpr
    change ((g : G) * t)⁻¹ * (t * (g : G)) ∈ J
    apply QuotientGroup.eq.mp
    have hc := Subgroup.mem_center_iff.mp hcentral (QuotientGroup.mk' J (g : G))
    change (QuotientGroup.mk ((g : G) * t) : G ⧸ J) = QuotientGroup.mk (t * (g : G)) at hc
    exact hc
  have hAodd : Odd (Nat.card A) := by
    have hRodd : Odd (Nat.card R) := hJodd.of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective J L.subtype L.subtype_injective)
    exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_le (show A ≤ R from inf_le_right))
  refine ⟨inferInstance, inferInstance, hAodd, inf_le_left, hBgen, ?_⟩
  exact central_mod_normal_intersection B R tL
    (generator_central_mod_normal B tL hBgen) hRcentral

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
