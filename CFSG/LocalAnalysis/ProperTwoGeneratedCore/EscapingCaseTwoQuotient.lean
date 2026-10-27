module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

abbrev escapingSylowImage (S : Sylow 2 G) (u : G) : Subgroup (EscapingQuotient u) :=
  ((S : Subgroup G).subgroupOf (Subgroup.centralizer ({u} : Set G))).map (escapingMk u)

theorem exists_sylow_eq_escapingSylowImage {S : Sylow 2 G} {u : G}
    (hsyl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) :
        Subgroup G)) :
    ∃ T : Sylow 2 (EscapingQuotient u),
      (T : Subgroup (EscapingQuotient u)) = escapingSylowImage S u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_subgroupOf inf_le_right (S.isPGroup'.to_le inf_le_left) hsyl
  refine ⟨Q.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective, hQ, Subgroup.inf_subgroupOf_right]

omit [Finite G] in
theorem escapingSylowImage_le_image {S : Sylow 2 G} {H : Subgroup G} {u : G}
    (hSH : (S : Subgroup G) ≤ H) : escapingSylowImage S u ≤ escapingImage H u :=
  Subgroup.map_mono fun _ ht => hSH ht

omit [Finite G] in
theorem mk_mem_centralizer_escapingSylowImage {S : Sylow 2 G} {u : G}
    {w : Subgroup.centralizer ({u} : Set G)} (hw : ∀ s ∈ (S : Subgroup G), s * w = w * s) :
    escapingMk u w ∈ Subgroup.centralizer (escapingSylowImage S u : Set (EscapingQuotient u)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨t, ht, rfl⟩
  have htw : t * w = w * t := Subtype.ext (hw t ht)
  rw [← map_mul, ← map_mul, htw]

namespace EscapingQuotientData

variable {H : Subgroup G} {x : G}

section HighRank

variable (hq : EscapingQuotientData H x) {J : Subgroup (EscapingQuotient x)}
  (hJ : CFSG.IsComponent J) (hrank : 2 ≤ CFSG.Open.pRank 2 J)
include hq hJ hrank

theorem component_characteristic_of_two_le_pRank : J.Characteristic := by
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  exact proper_full_core_high_rank_component_characteristic U _ hq.image_ne_top hUH hcore J
    ((CFSG.isComponent_iff_open J).mp hJ) hrank

theorem component_normal_of_two_le_pRank : J.Normal := by
  have := hq.component_characteristic_of_two_le_pRank hJ hrank
  infer_instance

theorem eq_bar_of_mem_centralizer_of_two_le_pRank {k : EscapingQuotient x}
    (hk : k ∈ Subgroup.centralizer (J : Set (EscapingQuotient x))) (hk2 : orderOf k = 2) :
    k = escapingBar x := by
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  have := hq.component_normal_of_two_le_pRank hJ hrank
  have hle := normal_rank_two_centralizer_rank_le_one U _ hq.image_ne_top hUH hcore J hrank
  by_contra hne
  have h := two_le_pRank_of_commuting_involutions hk hq.bar_mem_component_centralizer
    hk2 hq.bar_order hne (hq.commute_bar k)
  omega

end HighRank

end EscapingQuotientData

end CFSG.ProperTwoGeneratedCore.Assembly
