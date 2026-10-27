module

import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8Field

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem neighbourOvergroupSLmField_five_of_pPrimeCore_eq_bot (hcat : SLmCatalogueClausesAt 5)
    (hdet : SLmEvenTypeDetAt 5) {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    (hDm : LieModel (D ⧸ center D) .PSL 5 2 1) :
    NeighbourOvergroupSLmField s D 5 1 ∧ center D = ⊥ :=
  (neighbour_overgroup_slm_center_of_pPrimeCore_eq_bot (by norm_num) (Or.inl le_rfl) hcat hO hsec
    hs hD hsyl hstd hnn hDm).field hO hs hD (by norm_num) (Or.inl le_rfl) hdet hDm

section Hat

variable {G : Type} [Group G]

abbrev seitzBar (W : Subgroup G) : Type :=
  normalizer (W : Set G) ⧸ W.subgroupOf (normalizer (W : Set G))

abbrev seitzHat (W : Subgroup G) : Type :=
  seitzBar W ⧸ oddCore (seitzBar W)

@[expose] noncomputable def seitzHatMap (W : Subgroup G) : normalizer (W : Set G) →* seitzHat W :=
  (QuotientGroup.mk' (oddCore (seitzBar W))).comp
    (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))

theorem seitzHatMap_surjective (W : Subgroup G) : Function.Surjective (seitzHatMap W) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem pPrimeCore_two_seitzHat_eq_bot [Finite G] (W : Subgroup G) :
    pPrimeCore 2 (seitzHat W) = ⊥ :=
  F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _

theorem catalog_center_quotient_of_kProper_of_onto
    (hKP : CFSG.Assembly.KProper Catalog G) {H : Subgroup G} (hH : H ≠ ⊤) {Y : Type} [Group Y]
    {π : H →* Y} (hπ : Function.Surjective π) {Kc : Subgroup Y} (hKc : IsQuasisimple Kc) :
    Catalog (Kc ⧸ center Kc) := by
  have : IsSimpleGroup (Kc ⧸ center Kc) := hKc.2.1
  set M : Subgroup G := (Kc.comap π).map H.subtype with hM
  have hMH : M ≤ H := map_subtype_le _
  have hMtop : M ≠ ⊤ := fun h => hH (top_unique (h ▸ hMH))
  have hmem : ∀ m : M, (π.comp (Subgroup.inclusion hMH)) m ∈ Kc := by
    rintro ⟨_, h, hh, rfl⟩
    exact hh
  let ψ : M →* Kc := (π.comp (Subgroup.inclusion hMH)).codRestrict Kc hmem
  let φ : M →* Kc ⧸ center Kc := (QuotientGroup.mk' (center Kc)).comp ψ
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center Kc) z
    obtain ⟨h, hh⟩ := hπ (k : Y)
    have hhK : h ∈ Kc.comap π := by
      rw [mem_comap, hh]
      exact k.2
    refine ⟨⟨(h : G), h, hhK, rfl⟩, ?_⟩
    change QuotientGroup.mk' (center Kc) (ψ _) = QuotientGroup.mk' (center Kc) k
    congr 1
    exact Subtype.ext hh
  exact EvenSmallLie.CatalogOrders.catalog_of_kProper_of_surjective hKP M hMtop _ hKc.2.2 φ hφ

theorem lieModel_quotient_center_map_of_ne_bot {H Y : Type} [Group H] [Group Y] (φ : H →* Y)
    {D : Subgroup H} (hDq : CFSG.IsQuasisimple D) {m f : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) (hne : D.map φ ≠ ⊥) :
    LieModel ((D.map φ) ⧸ center (D.map φ)) .PSL m 2 f := by
  have hnt : ∃ k, φ.subgroupMap D k ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_bot_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact (mem_bot).mpr (congrArg Subtype.val (h ⟨d, hd⟩))
  obtain ⟨e₂⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hDq
    (φ.subgroupMap D) (φ.subgroupMap_surjective _)
    (LieType.CurtisTits.ker_le_center_of_isQuasisimple hDq hnt)
  exact LieType.CurtisTits.lieModel_of_mulEquiv e₂ hDm

theorem normalizer_ne_top_of_isSimpleGroup (hG : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {W : Subgroup G} (hW : W ≠ ⊥)
    (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) : normalizer (W : Set G) ≠ ⊤ := by
  intro htop
  have hWn : W.Normal := normalizer_eq_top_iff.mp htop
  rcases hG.eq_bot_or_eq_top_of_normal W with h | h
  · exact hW h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact hab (hWc a (h ▸ mem_top a) b (h ▸ mem_top b))

variable [Finite G]

theorem neighbourOvergroupSLmField_five_seitzHat (hcat : SLmCatalogueClausesAt 5)
    (hdet : SLmEvenTypeDetAt 5) (hG : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper Catalog G) {W : Subgroup G} (hW : W ≠ ⊥)
    (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) {t : G} (htN : t ∈ normalizer (W : Set G))
    (ht : orderOf (seitzHatMap W ⟨t, htN⟩) = 2) {D : Subgroup G}
    (hDN : D ≤ normalizer (W : Set G)) (hDq : CFSG.IsQuasisimple D)
    (hDm : LieModel (D ⧸ center D) .PSL 5 2 1)
    (hcomp : CFSG.Open.IsComponentOf ((D.subgroupOf (normalizer (W : Set G))).map (seitzHatMap W))
      (centralizer ({seitzHatMap W ⟨t, htN⟩} : Set (seitzHat W))))
    (hsyl : ∀ U : Subgroup (seitzHat W), IsPGroup 2 U →
      U ≤ centralizer (((D.subgroupOf (normalizer (W : Set G))).map (seitzHatMap W) :
        Subgroup (seitzHat W)) : Set (seitzHat W)) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard
      ((D.subgroupOf (normalizer (W : Set G))).map (seitzHatMap W)))
    (hnn : ¬ ((D.subgroupOf (normalizer (W : Set G))).map (seitzHatMap W)).Normal) :
    NeighbourOvergroupSLmField (seitzHatMap W ⟨t, htN⟩)
        ((D.subgroupOf (normalizer (W : Set G))).map (seitzHatMap W)) 5 1 ∧
      center ((D.subgroupOf (normalizer (W : Set G))).map (seitzHatMap W)) = ⊥ := by
  have hNtop := normalizer_ne_top_of_isSimpleGroup hG hnonab hW hWc
  have hsec : ∀ Kc : Subgroup (seitzHat W), IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => catalog_center_quotient_of_kProper_of_onto hKP hNtop
      (seitzHatMap_surjective W) hKc.1
  have hD₁ : CFSG.IsQuasisimple (D.subgroupOf (normalizer (W : Set G))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDN).symm hDq
  have hDm₁ : LieModel ((D.subgroupOf (normalizer (W : Set G))) ⧸
      center (D.subgroupOf (normalizer (W : Set G)))) .PSL 5 2 1 :=
    lieModel_quotient_center_congr (subgroupOfEquivOfLe hDN).symm hDm
  exact neighbourOvergroupSLmField_five_of_pPrimeCore_eq_bot hcat hdet
    (pPrimeCore_two_seitzHat_eq_bot W) hsec ht hcomp hsyl hstd hnn
    (lieModel_quotient_center_map_of_ne_bot _ hD₁ hDm₁ (ne_bot_of_isQuasisimple hcomp.2.2))

end Hat

end CFSG.SeitzReduction.LinearPilot
