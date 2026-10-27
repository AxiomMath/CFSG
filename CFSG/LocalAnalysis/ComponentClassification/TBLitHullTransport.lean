module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerIsoCorrSylowGrowth

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise

variable {X : Type} [Group X]

theorem mem_oddCoreIn_subgroupOf_iff {Y H : Subgroup X} (hYH : Y ≤ H) (x : H) :
    x ∈ oddCoreIn (Y.subgroupOf H) ↔ (x : X) ∈ oddCoreIn Y := by
  change _ ↔ (x : X) ∈ (pPrimeCore 2 Y).map Y.subtype
  rw [← pPrimeCore_map_subgroupOf 2 Y H hYH]
  constructor
  · exact fun hx => mem_map_of_mem H.subtype hx
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem oddCoreIn_subgroupOf {Y H : Subgroup X} (hYH : Y ≤ H) :
    oddCoreIn (Y.subgroupOf H) = (oddCoreIn Y).subgroupOf H := by
  ext x
  rw [mem_oddCoreIn_subgroupOf_iff hYH, mem_subgroupOf]

theorem mem_zStarIn_subgroupOf_iff {Y H : Subgroup X} (hYH : Y ≤ H) (x : H) :
    x ∈ zStarIn (Y.subgroupOf H) ↔ (x : X) ∈ zStarIn Y := by
  have key : (zStarIn (Y.subgroupOf H)).map H.subtype = zStarIn Y := by
    have h1 := map_centralPreimage_mulEquiv (subgroupOfEquivOfLe hYH) (pPrimeCore 2 _)
      (pPrimeCore 2 Y) (pPrimeCore_map_iso 2 _)
    change ((centralPreimage (pPrimeCore 2 (Y.subgroupOf H))).map (Y.subgroupOf H).subtype).map
      H.subtype = (centralPreimage (pPrimeCore 2 Y)).map Y.subtype
    rw [← h1, map_map, map_map]
    rfl
  rw [← key]
  constructor
  · exact fun hx => mem_map_of_mem H.subtype hx
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem ActsProperly.subgroupOf {H : Subgroup X} {t : X} {E A B : Subgroup X} (htH : t ∈ H)
    (hEH : E ≤ H) (hAH : A ≤ H) (h : ActsProperly t E A B) :
    ActsProperly (⟨t, htH⟩ : H) (E.subgroupOf H) (A.subgroupOf H) (B.subgroupOf H) := by
  obtain ⟨hnorm, htriv, e, he, a, ha, hnt⟩ := h
  have hcl : ∀ g : H, g ∈ closure (insert (⟨t, htH⟩ : H) ((E.subgroupOf H : Subgroup H) : Set H)) →
      (g : X) ∈ closure (insert t (E : Set X)) := by
    intro g hg
    have h1 : (closure (insert (⟨t, htH⟩ : H) ((E.subgroupOf H : Subgroup H) : Set H))).map
        H.subtype ≤ closure (insert t (E : Set X)) := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with rfl | hy
      · exact subset_closure (Set.mem_insert _ _)
      · exact subset_closure (Set.mem_insert_of_mem _ hy)
    exact h1 (mem_map_of_mem _ hg)
  refine ⟨fun g hg => ?_, fun g hg hgt => ?_, ⟨e, hEH he⟩, he, ⟨a, hAH ha⟩, ha, hnt⟩
  · obtain ⟨hgA, hgB⟩ := hnorm (hcl g hg)
    exact ⟨UnbalancedLayer.mem_normalizer_subgroupOf_of_mem hgA,
      UnbalancedLayer.mem_normalizer_subgroupOf_of_mem hgB⟩
  · exact htriv _ (hcl g hg) (fun x hx => hgt ⟨x, hAH hx⟩ hx)

theorem isSubnormal_subgroupOf_subgroupOf {A B H : Subgroup X} (hBH : B ≤ H)
    (h : (A.subgroupOf B).IsSubnormal) :
    ((A.subgroupOf H).subgroupOf (B.subgroupOf H)).IsSubnormal := by
  have heq : (A.subgroupOf H).subgroupOf (B.subgroupOf H) =
      (A.subgroupOf B).comap (subgroupOfEquivOfLe hBH).toMonoidHom := by
    ext x
    rfl
  rw [heq]
  exact h.comap _

theorem inf_centralizer_subgroupOf {A H : Subgroup X} {δ : X} (hδH : δ ∈ H) :
    (A ⊓ centralizer ({δ} : Set X)).subgroupOf H =
      A.subgroupOf H ⊓ centralizer ({(⟨δ, hδH⟩ : H)} : Set H) := by
  ext x
  simp only [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.1, Subtype.ext h.2⟩, fun h => ⟨h.1, congrArg Subtype.val h.2⟩⟩

theorem rangeRestrict_ne_one_of_not_trivial [Finite X] {Y H : Subgroup X} (hYH : Y ≤ H)
    [(Y.subgroupOf H).Normal] (hq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y)) {g : X} (hgH : g ∈ H)
    (hgY : g ∈ normalizer (Y : Set X)) (h : ¬ ∀ y ∈ Y, ⁅y, g⁆ ∈ oddCoreIn Y) :
    (conjQuotAction (Y.subgroupOf H)
      (centralPreimage (pPrimeCore 2 (Y.subgroupOf H)))).rangeRestrict ⟨g, hgH⟩ ≠ 1 := by
  intro h1
  have h2 : conjQuotAction (Y.subgroupOf H) (centralPreimage (pPrimeCore 2 (Y.subgroupOf H)))
      ⟨g, hgH⟩ = 1 := congrArg Subtype.val h1
  rw [conjQuotAction_eq_one_iff] at h2
  apply h
  refine forall_mem_oddCoreIn_of_forall_mem_zStarIn hq hgY fun y hy => ?_
  have h3 := h2 ⟨y, hYH hy⟩ hy
  rwa [mem_zStarIn_subgroupOf_iff hYH] at h3

theorem exists_ne_comm_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ s t : B, s * t ≠ t * s) : ∃ s t : A, s * t ≠ t * s := by
  obtain ⟨s, t, hst⟩ := h
  refine ⟨e.symm s, e.symm t, fun h1 => hst ?_⟩
  have h2 := congrArg e h1
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2

theorem hull_data [Finite X] {b a : X} {Y E : Subgroup X} (hC : IsUnbalancingConfig b a Y E)
    [hYn : (Y.subgroupOf (hull Y a E)).Normal] (hodd : OddLieType (Y ⧸ Open.fusionZStar Y))
    (hnot : ∀ p f : ℕ, p.Prime → p ≠ 2 → ¬ LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) :
    IsQuasisimple (Y.subgroupOf (hull Y a E) ⧸ pPrimeCore 2 (Y.subgroupOf (hull Y a E))) ∧
      center (Y.subgroupOf (hull Y a E) ⧸
        centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E)))) = ⊥ ∧
      IsM4 (conjQuotAction (Y.subgroupOf (hull Y a E))
        (centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E))))).range ∧
      orderOf ((conjQuotAction (Y.subgroupOf (hull Y a E))
        (centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E))))).rangeRestrict
          ⟨a, mem_hull_elem Y a E⟩) = 2 ∧
      (E.subgroupOf (hull Y a E)).map (conjQuotAction (Y.subgroupOf (hull Y a E))
          (centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E))))).rangeRestrict ≤
        oddCentralizerCore ((conjQuotAction (Y.subgroupOf (hull Y a E))
          (centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E))))).rangeRestrict
            ⟨a, mem_hull_elem Y a E⟩) := by
  obtain ⟨-, -, -, hYb, hY, -⟩ := id hC
  obtain ⟨hYn', hHb, hS, ⟨eF⟩, hαa, hEE', hE1, hEcore⟩ := config_odd_two_quotient hC
  obtain rfl : hYn' = hYn := Subsingleton.elim _ _
  have hq := hull_quasisimple hYb hY (le_hull_left Y a E)
  have : IsSimpleGroup (hullSection Y (hull Y a E)) := hS.1
  have hZ : center (hullSection Y (hull Y a E)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (hullSection Y (hull Y a E)))
      with h | h
    · exact h
    · exfalso
      obtain ⟨s, t, hst⟩ := hS.2
      exact hst (mem_center_iff.mp (h ▸ mem_top t) s)
  let e : GeneralizedFitting.subgroup (conjQuotAction (Y.subgroupOf (hull Y a E))
      (centralPreimage (pPrimeCore 2 (Y.subgroupOf (hull Y a E))))).range ≃*
      Y ⧸ Open.fusionZStar Y := eF.trans (hullSectionEquiv (le_hull_left Y a E))
  refine ⟨hq, hZ, ⟨eF.isSimpleGroup, ?_, oddLieType_of_mulEquiv e.symm hodd,
    fun p f hp hp2 hm => hnot p f hp hp2 (LieType.CurtisTits.lieModel_of_mulEquiv e hm), ?_⟩,
    ?_, ?_⟩
  · exact exists_ne_comm_of_mulEquiv eF hS.2
  · refine ⟨MonoidHom.rangeRestrict _ ⟨a, mem_hull_elem Y a E⟩, ?_, ?_⟩
    · rw [← orderOf_injective _ (MonoidHom.range _).subtype_injective]
      exact hαa
    · rw [oddCore_eq_pPrimeCore_two]
      exact ne_bot_of_le_map_subtype hE1 hEcore
  · rw [← orderOf_injective _ (MonoidHom.range _).subtype_injective]
    exact hαa
  · exact (map_mono hEE').trans hEcore

end CFSG.ComponentClassification.TBLit
