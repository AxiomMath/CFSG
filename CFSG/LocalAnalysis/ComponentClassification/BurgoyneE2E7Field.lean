module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Row
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Glue

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.UnbalancedCatalog (mem_zpowers_of_fixed)
open scoped MatrixGroups


theorem pPrimeCore_entrywiseFixedGroup_eq_bot {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) : pPrimeCore 2 (entrywiseFixedGroup .E7 σ) = ⊥ := by
  classical
  have : Finite (ModGL .E7 K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, -, hJn, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup .E7 K σ
  have hk2 := ringChar_fixSubfield_ne_two hK σ
  have hkodd : Odd (Nat.card (fixSubfield σ)) := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hk2
  obtain ⟨hsimp, hnab, -⟩ := odd_pinned_Chevalley_p_components .E7 (fixSubfield σ) hk2
  obtain ⟨-, -, hfaith, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7
    (fixSubfield σ) hkodd K (fixSubfield σ).subtype
  set Γ := entrywiseFixedGroup .E7 σ with hΓ
  set J' := (fixedFieldImage .E7 σ).subgroupOf Γ with hJ'
  let e : J' ≃* adjointGroup .E7 (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJΓ).trans
      (Subgroup.equivMapOfInjective (adjointGroup .E7 (fixSubfield σ)) _ hinj).symm
  have hJsimp : IsSimpleGroup J' := by
    have := hsimp
    exact e.isSimpleGroup
  have hJeven : Even (Nat.card J') := by
    rw [Nat.card_congr e.toEquiv]
    exact even_card_of_isQuasisimple (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  rw [pPrimeCore_eq_bot_iff]
  intro N hNn hNodd
  have hNJ : N ⊓ J' = ⊥ := by
    have hn : ((N ⊓ J').subgroupOf J').Normal := by
      refine (normal_subgroupOf_iff inf_le_right).2 fun h k hh hk => ?_
      exact Subgroup.mem_inf.2 ⟨hNn.conj_mem _ (Subgroup.mem_inf.1 hh).1 k,
        J'.mul_mem (J'.mul_mem hk (Subgroup.mem_inf.1 hh).2) (J'.inv_mem hk)⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ J').subgroupOf J') with h | h
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : J') ∈ (N ⊓ J').subgroupOf J' := hx
      rw [h, mem_bot] at this
      rw [mem_bot]
      exact congrArg Subtype.val this
    · exfalso
      have hle : J' ≤ N := fun x hx => by
        have : (⟨x, hx⟩ : J') ∈ (N ⊓ J').subgroupOf J' := by rw [h]; exact mem_top _
        exact this.1
      have hdvd : Nat.card J' ∣ Nat.card N := Subgroup.card_dvd_of_le hle
      exact (Nat.not_even_iff_odd.2 (Nat.coprime_two_left.1 (hNodd.coprime_dvd_right hdvd)))
        hJeven
  rw [eq_bot_iff]
  intro n hn
  have hcomm : ∀ j ∈ J', n * j = j * n := by
    intro j hj
    have h1 : n * j * n⁻¹ * j⁻¹ ∈ N ⊓ J' := by
      refine ⟨?_, ?_⟩
      · have := mul_mem hn (hNn.conj_mem _ (inv_mem hn) j)
        rwa [show n * (j * n⁻¹ * j⁻¹) = n * j * n⁻¹ * j⁻¹ by group] at this
      · exact J'.mul_mem (hJn.conj_mem j hj n) (J'.inv_mem hj)
    rw [hNJ, mem_bot] at h1
    calc n * j = n * j * n⁻¹ * j⁻¹ * (j * n) := by group
      _ = j * n := by rw [h1, one_mul]
  have hz : (n : ModGL .E7 K) = 1 := by
    refine hfaith _ (mem_inf.1 n.2).1 fun h hh => ?_
    have hhΓ : h ∈ Γ := hJΓ hh
    have := hcomm ⟨h, hhΓ⟩ hh
    exact congrArg Subtype.val this
  rw [mem_bot]
  exact Subtype.ext hz

theorem eq_one_of_odd_fix_fixedFieldImage {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {δ : K ≃+* K} (hδ : δ * δ = 1) {η : MulAut (adjointGroup .E7 K)} (hη : Odd (orderOf η))
    (hfix : ∀ x : adjointGroup .E7 K, (x : ModGL .E7 K) ∈ fixedFieldImage .E7 δ → η x = x) :
    η = 1 := by
  classical
  have hτ : Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 := Or.inr (Or.inl rfl)
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form .E7 hτ K
  obtain ⟨Θ, -, hΘ, -, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E7 hτ K
  obtain ⟨g, a, σ, ε, hexpr⟩ := hNF η
  have hσk : ∀ c, δ c = c → σ c = c := by
    have hcl := (ordinary_E_root_SL2_full_module_traces_all_characteristics .E7 hτ).2
      (fixSubfield δ) K (e7Node 0) 1 1
    have hS : {x : K | ∃ A : SL2 (fixSubfield δ), x = LinearMap.trace K (RootModule .E7 K)
        ((1 * simpleRootSL2 .E7 K (e7Node 0) (conjGL 1 (Matrix.SpecialLinearGroup.map
          (algebraMap (fixSubfield δ) K) A)) * 1⁻¹ : ModGL .E7 K) :
            Module.End K (RootModule .E7 K))} ⊆
        ((RingHom.eqLocusField σ.toRingHom (RingHom.id K) : Subfield K) : Set K) := by
      rintro _ ⟨A, rfl⟩
      set y := simpleRootSL2 .E7 (fixSubfield δ) (e7Node 0) A with hy
      have hyC : y ∈ adjointGroup .E7 (fixSubfield δ) := simpleRootSL2_mem_adjointGroup _ A
      have hxJ : baseChangeGL (fixSubfield δ).subtype y ∈ fixedFieldImage .E7 δ := ⟨_, hyC, rfl⟩
      have hxC := (fixedFieldImage_le hxJ).1
      have htr := RankThree.PartOne.KE.trace_apply_of_expression η g a σ ε hexpr ⟨_, hxC⟩
      rw [hfix ⟨_, hxC⟩ hxJ] at htr
      have he : (1 * simpleRootSL2 .E7 K (e7Node 0) (conjGL 1 (Matrix.SpecialLinearGroup.map
          (algebraMap (fixSubfield δ) K) A)) * 1⁻¹ : ModGL .E7 K) =
            baseChangeGL (fixSubfield δ).subtype y := by
        rw [hy, conjGL_one', one_mul, inv_one, mul_one, baseChangeGL_simpleRootSL2]
        rfl
      change σ _ = _
      rw [he]
      exact htr.symm
    have hle := Subfield.closure_le.2 hS
    rw [hcl] at hle
    intro c hc
    exact hle ⟨⟨c, hc⟩, rfl⟩
  have hσ2 : σ ^ 2 = 1 := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_fixed hσk)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hδ, one_zpow]
  have hσn : σ ^ orderOf η = 1 := by
    have h := congrArg Prod.fst (map_pow Θ η (orderOf η))
    rw [pow_orderOf_eq_one, map_one, hΘ η g a σ ε hexpr] at h
    simpa using h.symm
  have hσ1 : σ = 1 := by
    have h1 : orderOf σ ∣ 1 := by
      rw [← (Nat.coprime_two_right.2 hη).gcd_eq_one]
      exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσn) (orderOf_dvd_of_pow_eq_one hσ2)
    rwa [Nat.dvd_one, orderOf_eq_one_iff] at h1
  subst hσ1
  have hQ : exactQ .E7 K (ε : ℕ) = 1 := rfl
  have h1 : ∀ x : ModGL .E7 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hη' : η = MulAut.conj g * rootDiagAut .E7 K a := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hexpr x, hQ, mul_one, inv_one, mul_one, h1, MulAut.mul_apply, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_mul, coe_rootDiagAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  obtain ⟨Φ, -, hkerΦ, hdvd⟩ := exists_outer_hom_E (τ := .E7) (K := K) hτ
  have hmem : QuotientGroup.mk' (inner (adjointGroup .E7 K)) η ∈ Φ.ker := by
    rw [hkerΦ]
    refine ⟨a, ?_⟩
    rw [hη']
    change (QuotientGroup.mk (rootDiagAut .E7 K a) : Outer (adjointGroup .E7 K)) =
      QuotientGroup.mk' (inner (adjointGroup .E7 K)) (MulAut.conj g * rootDiagAut .E7 K a)
    rw [map_mul, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff
      (N := inner (adjointGroup .E7 K)) (MulAut.conj g)).2 (MonoidHom.mem_range.2 ⟨g, rfl⟩),
      one_mul]
    rfl
  have hord : orderOf (QuotientGroup.mk' (inner (adjointGroup .E7 K)) η) = 1 := by
    have h2 : orderOf (QuotientGroup.mk' (inner (adjointGroup .E7 K)) η) ∣ 2 := by
      refine (Subgroup.orderOf_dvd_natCard _ hmem).trans ?_
      rw [det_cartan_E7] at hdvd
      exact hdvd
    have hodd : Odd (orderOf (QuotientGroup.mk' (inner (adjointGroup .E7 K)) η)) :=
      Odd.of_dvd_nat hη (orderOf_map_dvd _ η)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hord
  obtain ⟨g', rfl⟩ := hord
  have hk2 := ringChar_fixSubfield_ne_two hK δ
  have hkodd : Odd (Nat.card (fixSubfield δ)) := by
    have : Fintype (fixSubfield δ) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hk2
  obtain ⟨-, -, hfaith, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7
    (fixSubfield δ) hkodd K (fixSubfield δ).subtype
  have hg' : (g' : ModGL .E7 K) = 1 := by
    refine hfaith _ g'.2 fun h hh => ?_
    have hhC : h ∈ adjointGroup .E7 K := (fixedFieldImage_le hh).1
    have hc := congrArg Subtype.val (hfix ⟨h, hhC⟩ hh)
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hc
    calc (g' : ModGL .E7 K) * h = (g' * h * (g' : ModGL .E7 K)⁻¹) * g' := by group
      _ = h * g' := by rw [hc]
  rw [show g' = 1 from Subtype.ext hg', map_one]

theorem burgCoreFor_entrywise {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {δ : K ≃+* K} (hδ : δ * δ = 1) {β : MulAut (adjointGroup .E7 K)}
    (hβ : ∀ u, (β u : ModGL .E7 K) = Units.map (entrywiseHom δ.toRingHom) (u : ModGL .E7 K)) :
    BurgCoreFor β := by
  have hmem : ∀ u : adjointGroup .E7 K, u ∈ fixedSubgroup β ↔
      (u : ModGL .E7 K) ∈ entrywiseFixedGroup .E7 δ := by
    intro u
    rw [mem_entrywiseFixedGroup]
    change β u = u ↔ _
    rw [← Subtype.coe_inj, hβ]
    exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
  let e : fixedSubgroup β ≃* entrywiseFixedGroup .E7 δ :=
    { toFun := fun u => ⟨u.1.1, (hmem u.1).1 u.2⟩
      invFun := fun x => ⟨⟨x.1, (mem_entrywiseFixedGroup.1 x.2).1⟩, (hmem _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨?_, fun η hη _ hfix => eq_one_of_odd_fix_fixedFieldImage hK hδ hη fun x hx =>
    hfix x ((hmem x).2 (fixedFieldImage_le hx))⟩
  have h := pPrimeCore_map_iso 2 e
  rw [pPrimeCore_entrywiseFixedGroup_eq_bot hK δ] at h
  exact (map_eq_bot_iff_of_injective _ e.injective).1 h

theorem burgCoreFor_E7_field {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {K : Type} [Field K]
    [Finite K] (hK2 : ringChar K ≠ 2) (hK : Nat.card K = (p ^ e) ^ 2) {δ : K ≃+* K}
    (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup .E7 K)} {g : adjointGroup .E7 K}
    {a : Fin Tag.E7.rank → Kˣ}
    (hαg : ∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) = (g : ModGL .E7 K) *
      rootDiagUnit .E7 a * Units.map (entrywiseHom δ.toRingHom) (h : ModGL .E7 K) *
        (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹)
    (hα : α ^ 2 = 1) : BurgCoreFor α := by
  classical
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hK δ.toRingHom hδ
  obtain ⟨β, hβ, hα'⟩ := hQ1 .E7
  obtain ⟨-, hconj⟩ := hα' g a
  obtain ⟨ψ, hψ, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hψβ : ψ * α * ψ⁻¹ = β := MulEquiv.ext fun u => Subtype.ext ((hψ u).trans (hβ u).symm)
  have : Fintype K := Fintype.ofFinite K
  have hδ2 : δ * δ = 1 := RingEquiv.ext fun c => by
    rw [RingAut.mul_apply, hδ, hδ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have h := (burgCoreFor_entrywise hK2 hδ2 hβ).conj ψ⁻¹
  rwa [← hψβ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at h

end CFSG.ComponentClassification.Burgoyne.E2
