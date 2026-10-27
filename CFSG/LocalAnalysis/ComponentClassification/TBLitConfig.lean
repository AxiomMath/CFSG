module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepOne

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement

variable {X : Type} [Group X]

abbrev oddCentralizerCore (a : X) : Subgroup X :=
  (pPrimeCore 2 (centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype

@[expose] def IsUnbalancingConfig (b a : X) (Y E : Subgroup X) : Prop :=
  orderOf b = 2 ∧ orderOf a = 2 ∧ a * b = b * a ∧ Y ≤ centralizer ({b} : Set X) ∧
    IsPComponent 2 (Y.subgroupOf (centralizer ({b} : Set X))) ∧ E ≤ oddCentralizerCore a ∧
    E ≤ centralizer ({b} : Set X) ∧ ⁅Y, zpowers a⁆ = Y ∧ ⁅Y, E⁆ = Y

theorem isUnbalancingConfig_of_triple {x y : X} {L : Subgroup X}
    (hT : UnbalancedLayer.GSUnbalancingTriple x y L) :
    IsUnbalancingConfig x y L (oddCentralizerMeet x y) := by
  obtain ⟨hx, hy, hxy, hLx, hL, hLy, hLD⟩ := UnbalancedLayer.gsUnbalancingTriple_iff.mp hT
  exact ⟨hx, hy, hxy.symm, hLx, hL, inf_le_left, inf_le_right, hLy, hLD⟩

theorem conj_mem_oddCentralizerCore {a g e : X} (hg : g ∈ centralizer ({a} : Set X))
    (he : e ∈ oddCentralizerCore a) : g * e * g⁻¹ ∈ oddCentralizerCore a := by
  obtain ⟨e', he', rfl⟩ := he
  refine ⟨⟨g, hg⟩ * e' * ⟨g, hg⟩⁻¹, (inferInstance : (pPrimeCore 2 _).Normal).conj_mem e' he' _,
    ?_⟩
  simp

theorem coprime_card_oddCentralizerCore [Finite X] (a : X) :
    Nat.Coprime 2 (Nat.card (oddCentralizerCore a)) := by
  rw [card_map_of_injective (centralizer ({a} : Set X)).subtype_injective]
  exact pPrimeCore_coprime_card

theorem config_odd_two_quotient [Finite X] {b a : X} {Y E : Subgroup X}
    (hC : IsUnbalancingConfig b a Y E) :
    ∃ hYn : (Y.subgroupOf (hull Y a E)).Normal,
      let H := hull Y a E
      let α := @conjQuotAction H _ (Y.subgroupOf H) hYn
        (centralPreimage (pPrimeCore 2 (Y.subgroupOf H))) _
      let aH : H := ⟨a, mem_hull_elem Y a E⟩
      let E' : Subgroup H := (oddCentralizerCore a).subgroupOf H
      H ≤ centralizer ({b} : Set X) ∧
        (IsSimpleGroup (hullSection Y H) ∧ ∃ s t : hullSection Y H, s * t ≠ t * s) ∧
        Nonempty (GeneralizedFitting.subgroup α.range ≃* hullSection Y H) ∧
        orderOf (α aH) = 2 ∧ E.subgroupOf H ≤ E' ∧
        E'.map α.rangeRestrict ≠ ⊥ ∧
        E'.map α.rangeRestrict ≤
          (pPrimeCore 2 (centralizer {α.rangeRestrict aH})).map
            (centralizer {α.rangeRestrict aH}).subtype := by
  obtain ⟨-, ha, hab, hYb, hY, hEa, hEb, hYa, hYE⟩ := hC
  have hYn : (Y.subgroupOf (hull Y a E)).Normal := hull_normal hYa.le hYE.le
  refine ⟨hYn, ?_⟩
  intro H α aH E'
  have hYH : Y ≤ H := le_hull_left Y a E
  have hEH : E ≤ H := le_hull_right Y a E
  have hHb : H ≤ centralizer ({b} : Set X) :=
    sup_le (sup_le hYb (zpowers_le.mpr (mem_centralizer_singleton.mpr hab))) hEb
  have hQ := hull_quasisimple hYb hY hYH
  obtain ⟨hS, -, -, -, -, -, -, -, hF, ⟨f⟩, hy1, hD1⟩ :=
    normal_quasisimple_section_automorphism_image (Y.subgroupOf H) (pPrimeCore 2 (Y.subgroupOf H))
      hQ
  have haH : orderOf aH = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ha
  have hEE' : E.subgroupOf H ≤ E' := fun e he => hEa he
  have hE'a : E' ≤ centralizer {aH} := by
    intro e he
    have h1 : (e : X) ∈ oddCentralizerCore a := he
    obtain ⟨e', -, he'⟩ := h1
    refine mem_centralizer_singleton.mpr (Subtype.ext ?_)
    have h2 := mem_centralizer_singleton.mp e'.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← he']
    exact h2
  have hE'n : (E'.subgroupOf (centralizer {aH})).Normal := by
    rw [normal_subgroupOf_iff hE'a]
    intro e c he hc
    have hca : (c : X) ∈ centralizer ({a} : Set X) :=
      mem_centralizer_singleton.mpr (congrArg Subtype.val (mem_centralizer_singleton.mp hc))
    exact conj_mem_oddCentralizerCore hca he
  have hE'odd : Nat.Coprime 2 (Nat.card E') := by
    have h1 : Nat.card E' ∣ Nat.card (oddCentralizerCore a) := by
      rw [← card_map_of_injective H.subtype_injective]
      exact card_dvd_of_le (by
        rw [subgroupOf_map_subtype]
        exact inf_le_left)
    exact (coprime_card_oddCentralizerCore a).coprime_dvd_right h1
  have hgen : Y.subgroupOf H ⊔ zpowers aH ⊔ E' = ⊤ :=
    top_le_iff.mp ((hull_sup_eq_top Y E a).symm ▸ sup_le_sup_left hEE' _)
  have hYa' : ⁅Y.subgroupOf H, zpowers aH⁆ = Y.subgroupOf H := hull_commutator_elem hYa
  have hYE' : ⁅Y.subgroupOf H, E'⁆ = Y.subgroupOf H := by
    apply le_antisymm
    · exact Subgroup.commutator_le_left _ _
    · calc Y.subgroupOf H = ⁅Y.subgroupOf H, E.subgroupOf H⁆ := (hull_commutator_right hYE).symm
        _ ≤ ⁅Y.subgroupOf H, E'⁆ := commutator_mono le_rfl hEE'
  have hcore := odd_two_quotient_core (hLn := hYn) hQ haH hE'a hE'n hE'odd hgen hYa' hYE'
  have hαE := map_rangeRestrict_le_of_ker_eq 2 (pPrimeCore 2 H) (pCore 2 (H ⧸ pPrimeCore 2 H)) α
    hcore.1 E' aH hcore.2
  have hαE1 : E'.map α.rangeRestrict ≠ ⊥ := by
    rw [ne_eq, map_rangeRestrict_eq_bot_iff]
    exact hD1 E' hYE'
  have haH2 : aH ^ 2 = 1 := by
    rw [← haH]
    exact pow_orderOf_eq_one aH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαa : orderOf (α aH) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, haH2, map_one]) (hy1 aH hYa')
  have hbridge : CFSG.generalizedFitting α.range = GeneralizedFitting.subgroup α.range :=
    CFSG.generalizedFitting_eq_componentClassification α.range
  exact ⟨hHb, hS, ⟨(MulEquiv.subgroupCongr (hbridge.symm.trans hF)).trans f⟩, hαa, hEE', hαE1,
    hαE⟩

theorem config_almost_simple [Finite X] {b a : X} {Y E : Subgroup X}
    (hC : IsUnbalancingConfig b a Y E) :
    hull Y a E ≤ centralizer ({b} : Set X) ∧
      (IsSimpleGroup (hullSection Y (hull Y a E)) ∧
        ∃ s t : hullSection Y (hull Y a E), s * t ≠ t * s) ∧
      ∃ (B : Type) (_ : Group B) (_ : Finite B),
        Nonempty (GeneralizedFitting.subgroup B ≃* hullSection Y (hull Y a E)) ∧
        ∃ z : B, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set B)) ≠ ⊥ := by
  obtain ⟨hYn, hHb, hS, hF, hαa, -, hE1, hEcore⟩ := config_odd_two_quotient hC
  refine ⟨hHb, hS, _, inferInstance, inferInstance, hF, MonoidHom.rangeRestrict _
    ⟨a, mem_hull_elem Y a E⟩, ?_, ?_⟩
  · rw [← orderOf_injective _ (MonoidHom.range _).subtype_injective]
    exact hαa
  · rw [oddCore_eq_pPrimeCore_two]
    exact ne_bot_of_le_map_subtype hE1 hEcore

theorem config_uList (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) [Finite X]
    (hK : Assembly.KProper Catalog X) {b a : X} (hbZ : b ∉ center X) {Y E : Subgroup X}
    (hC : IsUnbalancingConfig b a Y E) : UList (Y ⧸ Open.fusionZStar Y) := by
  obtain ⟨hHb, hS, B, _, _, ⟨eF⟩, hz⟩ := config_almost_simple hC
  have hHtop : hull Y a E ≠ ⊤ := (lt_of_le_of_lt hHb (centralizer_lt_top hbZ)).ne
  have hKH := kGroupOver_of_kProper SectionRank.catalog_of_mulEquiv catalog_of_abelian_simple hK
    _ hHtop
  have := hS.1
  have hcatS : Catalog (hullSection Y (hull Y a E)) := hKH _ _ hS.1
  have hsimple : IsSimpleGroup (GeneralizedFitting.subgroup B) := eF.isSimpleGroup
  have hnonab : ∃ s t : GeneralizedFitting.subgroup B, s * t ≠ t * s := by
    obtain ⟨s, t, hst⟩ := hS.2
    refine ⟨eF.symm s, eF.symm t, fun h => hst (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  exact uList_of_mulEquiv (eF.trans (hullSectionEquiv (le_hull_left Y a E)))
    (uList_of_uOutcome (hUc B hsimple hnonab (SectionRank.catalog_of_mulEquiv eF hcatS) hz))

end CFSG.ComponentClassification.TBLit
