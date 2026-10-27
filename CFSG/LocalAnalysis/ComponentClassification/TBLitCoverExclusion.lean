module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitCore

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem IsUnbalancingConfig.normalizes {b a : X} {Y E : Subgroup X}
    (hC : IsUnbalancingConfig b a Y E) :
    a ∈ normalizer (Y : Set X) ∧ E ≤ normalizer (Y : Set X) := by
  obtain ⟨-, -, -, -, -, -, -, hYa, hYE⟩ := id hC
  have hYn : (Y.subgroupOf (hull Y a E)).Normal := hull_normal hYa.le hYE.le
  have hJ : ∀ g : hull Y a E, (g : X) ∈ normalizer (Y : Set X) := fun g =>
    UnbalancedLayer.mem_normalizer_of_subgroupOf (le_hull_left Y a E) (by
      rw [normalizer_eq_top_iff.mpr hYn]
      exact mem_top g)
  exact ⟨hJ ⟨a, mem_hull_elem Y a E⟩, fun e he => hJ ⟨e, le_hull_right Y a E he⟩⟩

theorem exists_involution_lift_mk {M : Subgroup X} {a : X} (ha : a ^ 2 = 1)
    (haM : a ∈ normalizer (M : Set X)) {u : M ⧸ pPrimeCore 2 M} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hau : oddQuotAction M ⟨a, haM⟩ u = u) :
    ∃ δ : X, ∃ hδM : δ ∈ M, orderOf δ = 2 ∧ δ * a = a * δ ∧
      ((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M) = u := by
  obtain ⟨mu, hmu⟩ := QuotientGroup.mk_surjective u
  have hOMn : ((oddCoreIn M).subgroupOf M).Normal := by
    rw [show (oddCoreIn M).subgroupOf M = pPrimeCore 2 M from
      comap_map_eq_self_of_injective M.subtype_injective _]
    infer_instance
  have hamu : a * (mu : X) * a⁻¹ ∈ M := (mem_normalizer_iff.mp haM _).mp mu.2
  obtain ⟨δ, hδM, hδ2, hδa, hδmu⟩ := exists_involution_lift (oddCoreIn_le M) hOMn
    (odd_card_oddCoreIn M) ha (normalizer_le_normalizer_oddCoreIn M haM) mu.2
    (by
      have h1 : ((mu ^ 2 : M) : X) ∈ oddCoreIn M := by
        rw [mem_oddCoreIn_iff_mk, QuotientGroup.mk_pow, hmu, hu2]
      exact h1)
    (by
      intro h
      apply hu1
      rw [← hmu, ← mem_oddCoreIn_iff_mk]
      exact h)
    (by
      have h2 : ((⟨a * mu * a⁻¹, hamu⟩ : M) : M ⧸ pPrimeCore 2 M) =
          oddQuotAction M ⟨a, haM⟩ u := by
        rw [← hmu, oddQuotAction_mk]
      have h1 : ((mu⁻¹ * ⟨a * mu * a⁻¹, hamu⟩ : M) : X) ∈ oddCoreIn M := by
        rw [mem_oddCoreIn_iff_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h2, hau, hmu,
          inv_mul_cancel]
      exact h1)
  refine ⟨δ, hδM, hδ2, hδa, ?_⟩
  have h1 : (((⟨δ, hδM⟩ : M)⁻¹ * mu : M) : X) ∈ oddCoreIn M := hδmu
  rw [mem_oddCoreIn_iff_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmu,
    inv_mul_eq_one] at h1
  exact h1

theorem isPComponent_top_coreQuotient {C Y : Subgroup X} (hYC : Y ≤ C)
    (hY : IsPComponent 2 (Y.subgroupOf C)) :
    IsPComponent 2 (⊤ : Subgroup (Y ⧸ pPrimeCore 2 Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hY le_rfl
  rw [subgroupOf_self] at h1
  have h2 := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    (subgroupOfEquivOfLe hYC)).1 _).mp h1
  rw [Subgroup.map_top_of_surjective _ (subgroupOfEquivOfLe hYC).surjective] at h2
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 Y)).ker := by
    rw [QuotientGroup.ker_mk']
    intro h
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
  have h3 := (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (QuotientGroup.mk' (pPrimeCore 2 Y)) (QuotientGroup.mk'_surjective _) hker).1.mapsTo h2
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3

omit [Finite X] in
theorem exists_moved_of_commutator_eq {Y D : Subgroup X} (hD : D ≤ normalizer (Y : Set X))
    (hYD : ⁅Y, D⁆ = Y) (hnt : Nontrivial (Y ⧸ pPrimeCore 2 Y)) :
    ∃ d, ∃ hd : d ∈ D, ∃ x, oddQuotAction Y ⟨d, hD hd⟩ x ≠ x := by
  by_contra hall
  push Not at hall
  have hle : ⁅Y, D⁆ ≤ oddCoreIn Y := by
    rw [Subgroup.commutator_le]
    intro y hy d hd
    have h1 : oddQuotAction Y ⟨d, hD hd⟩ = 1 := MulEquiv.ext fun x => hall d hd x
    exact (oddQuotAction_eq_one_iff _).mp h1 y hy
  rw [hYD] at hle
  obtain ⟨x, y, hxy⟩ := hnt
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  rw [(mem_oddCoreIn_iff_mk x').mp (hle x'.2), (mem_oddCoreIn_iff_mk y').mp (hle y'.2)] at hxy
  exact hxy rfl

omit [Finite X] in
theorem exists_moved_of_commutator_zpowers_eq {Y : Subgroup X} {a : X}
    (haY : a ∈ normalizer (Y : Set X)) (hYa : ⁅Y, zpowers a⁆ = Y)
    (hnt : Nontrivial (Y ⧸ pPrimeCore 2 Y)) : ∃ x, oddQuotAction Y ⟨a, haY⟩ x ≠ x := by
  obtain ⟨d, hd, x, hx⟩ := exists_moved_of_commutator_eq (zpowers_le.mpr haY) hYa hnt
  by_contra hall
  push Not at hall
  have h1 : oddQuotAction Y ⟨a, haY⟩ = 1 := MulEquiv.ext fun x => hall x
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hd
  have h2 : (⟨d, zpowers_le.mpr haY hd⟩ : normalizer (Y : Set X)) = ⟨a, haY⟩ ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk.symm
  apply hx
  rw [h2, map_zpow, h1, one_zpow, MulAut.one_apply]

theorem false_of_quotient_component (hI : TBInputs)
    (hX : TBSetting X) {b a : X} {Y E : Subgroup X} (hC : IsUnbalancingConfig b a Y E)
    (haY : a ∈ normalizer (Y : Set X))
    (hEY : E ≤ normalizer (Y : Set X)) {γ : X} (hγY : γ ∈ Y) (hγ : orderOf γ = 2)
    (hγa : γ * a = a * γ) {T : Subgroup (Y ⧸ pPrimeCore 2 Y)}
    (hT : T ≤ centralizer ({((⟨γ, hγY⟩ : Y) : Y ⧸ pPrimeCore 2 Y)} : Set (Y ⧸ pPrimeCore 2 Y)))
    (hTc : IsPComponent 2 (T.subgroupOf
      (centralizer ({((⟨γ, hγY⟩ : Y) : Y ⧸ pPrimeCore 2 Y)} : Set (Y ⧸ pPrimeCore 2 Y)))))
    (hγT : ((⟨γ, hγY⟩ : Y) : Y ⧸ pPrimeCore 2 Y) ∈ T)
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) (eT : T ≃* SL(2, GaloisField p n))
    (haT : ∀ x ∈ T, oddQuotAction Y ⟨a, haY⟩ x ∈ T)
    (hET : ∀ e (he : e ∈ E), ∀ x ∈ T, oddQuotAction Y ⟨e, hEY he⟩ x ∈ T)
    (hant : ∃ x ∈ T, oddQuotAction Y ⟨a, haY⟩ x ≠ x)
    (hent : ∃ e, ∃ he : e ∈ E, ∃ x ∈ T, oddQuotAction Y ⟨e, hEY he⟩ x ≠ x) : False := by
  obtain ⟨hb, ha, hab, hYb, hYc, hEa, hEb, -, -⟩ := id hC
  have hγγ : γ * γ = 1 := by rw [← pow_two, ← hγ, pow_orderOf_eq_one]
  obtain ⟨N, -, hN, hNc, hNq, eN, hprop⟩ := lift_component ha hYb hYc hγY hγγ hγa haY hEa hEY
    hT hTc hp2 hn eT haT hET hant hent
  have hγN : γ ∈ N := mem_of_mem_quotImage hγY (by rw [pow_two]; exact hγγ)
    (fun x hx => mem_centralizer_singleton_iff.mp (mem_inf.mp (hN hx)).2)
    (by rw [hNq]; exact hγT)
  have hγbC : γ ∈ centralizer ({b} : Set X) := hYb hγY
  have hbγ : b * γ = γ * b := (mem_centralizer_singleton_iff.mp hγbC).symm
  exact CoreConfig.false hI hX (a := a) (b := b) (γ := γ) (S := N)
    (E := (E ⊔ conjugate E γ) ⊓ centralizer ({γ} : Set X)) ⟨ha, hb, hγ, hab, hγa.symm, hbγ, hN,
      hNc, hγN, ⟨p, n, inferInstance, hp2, hn, eN⟩,
      inf_le_left.trans (sup_le hEa (conjugate_le_oddCentralizerCore
        (mem_centralizer_singleton_iff.mpr hγa) hEa)),
      le_inf (inf_le_left.trans (sup_le hEb (conjugate_le_of_le_of_mem hEb hγbC))) inf_le_right,
      hprop⟩

theorem coverExclusion_of_inputs (hI : TBInputs) :
    CoverExclusion := by
  intro X _ _ _ hnonab hK hz hU b a Y E hC hcase
  have hX : TBSetting X := ⟨inferInstance, hnonab, hK, hz, hU⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hb, ha, hab, hYb, hYc, hEa, hEb, hYa, hYE⟩ := id hC
  rcases hcase with ⟨n, hn, h7, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hm⟩
  · exact center_coreQuotient_eq_bot_of_fusionZStar_eq Y
      (hI.solomon X hnonab hK hz hU b n Y hb hn h7 hYb hYc ⟨e⟩)
  by_contra hcen
  have hq := twoComponent_coreQuotient_quasisimple hYb hYc
  have hZ2 := center_isPGroup_two_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    (Q := Y ⧸ pPrimeCore 2 Y)
  obtain ⟨hf, hfact, ⟨eSL⟩⟩ := psl_two_double_cover hI.griessTable hI.griessCovers hq hZ2 hcen hp
    hp2 (LieType.CurtisTits.lieModel_of_mulEquiv (coreQuotientCenterEquiv Y).symm hm)
  obtain ⟨haY, hEY⟩ := hC.normalizes
  obtain ⟨z, -, hz2, hz1, hzc, hzu⟩ := exists_central_involution hp2 hf
    ((Subgroup.topEquiv).trans eSL)
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hφa2 : ∀ q, oddQuotAction Y ⟨a, haY⟩ (oddQuotAction Y ⟨a, haY⟩ q) = q := by
    intro q
    rw [oddQuotAction_mul_apply,
      show (⟨a * a, mul_mem haY haY⟩ : normalizer (Y : Set X)) = 1 from Subtype.ext ha2,
      map_one, MulAut.one_apply]
  have hfz := fixed_of_unique_central (mem_top z) hz1 hzc hzu (oddQuotAction Y ⟨a, haY⟩)
    (fun x _ => mem_top _) hφa2
  have hz2' : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz2] at h
  obtain ⟨γ, hγY, hγ, hγa, hγz⟩ := exists_involution_lift_mk (by rw [pow_two]; exact ha2) haY
    hz2' hz1 hfz
  have hT : (⊤ : Subgroup (Y ⧸ pPrimeCore 2 Y)) ≤
      centralizer ({((⟨γ, hγY⟩ : Y) : Y ⧸ pPrimeCore 2 Y)} : Set (Y ⧸ pPrimeCore 2 Y)) := by
    intro x _
    rw [mem_centralizer_singleton_iff, hγz]
    exact (hzc x (mem_top x)).symm
  have hTc := CatalogueBPrimeJoin.pComponent_restrict_overgroup 2
    (isPComponent_top_coreQuotient hYb hYc) hT
  have hnt : Nontrivial (Y ⧸ pPrimeCore 2 Y) := nontrivial_of_ne z 1 hz1
  obtain ⟨x, hx⟩ := exists_moved_of_commutator_zpowers_eq haY hYa hnt
  obtain ⟨e₀, he₀, x₀, hx₀⟩ := exists_moved_of_commutator_eq hEY hYE hnt
  exact false_of_quotient_component hI hX hC haY hEY hγY hγ hγa hT hTc (mem_top _) hp2 hf
    ((Subgroup.topEquiv).trans eSL) (fun _ _ => mem_top _) (fun _ _ _ _ => mem_top _)
    ⟨x, mem_top x, hx⟩ ⟨e₀, he₀, x₀, mem_top x₀, hx₀⟩

end CFSG.ComponentClassification.TBLit
