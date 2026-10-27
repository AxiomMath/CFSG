module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (d4_mem_trialityFieldImage_self_iff
  d4_trialityFieldImage_self_le)
open scoped Pointwise

section G2Class


variable {K : Type} [Field K] [Finite K]

theorem existsUnique_conj_mul_fieldActor_D4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃! gδ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom × (K ≃+* K),
      α = MulAut.conj gδ.1 * fieldActor σ gδ.2 := by
  by_cases h2 : ℓ = 2
  · subst h2
    exact (even_triality_exact_automorphism_normal_form hf K hK σ hσ).2.1 α
  · exact (odd_triality_exact_automorphism_normal_form hℓ h2 hf K hK σ hσ).2.1 α

theorem map_fixSub_fieldActor_self (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    (fixSub (fieldActor (t := TwistTag.D4) σ σ)).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = trialityFieldImage σ σ := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (d4_mem_trialityFieldImage_self_iff σ hσ3 g).2 hg
  · intro hx
    exact ⟨⟨x, d4_trialityFieldImage_self_le σ hx⟩,
      (d4_mem_trialityFieldImage_self_iff σ hσ3 _).1 hx, rfl⟩

theorem eq_one_of_fix_fixSub_fieldActor_self {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hcop : Nat.Coprime 3 (orderOf ζ))
    (hcomm : ζ * fieldActor (t := TwistTag.D4) σ σ = fieldActor σ σ * ζ)
    (hfix : ∀ t ∈ fixSub (fieldActor (t := TwistTag.D4) σ σ), ζ t = t) : ζ = 1 := by
  classical
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hσ₀3 : ∀ c : fixSubfield σ, fixSubfieldRestrict σ σ (fixSubfieldRestrict σ σ
      (fixSubfieldRestrict σ σ c)) = c := fun c => Subtype.ext (by
    simp only [coe_fixSubfieldRestrict]
    exact hσ3 c)
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hJC := d4_trialityFieldImage_self_le σ
  have hιinj : Function.Injective
      (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype) := baseChangeGL_injective _
  have hcommδ : ∀ φ : K ≃+* K, fieldActor (t := TwistTag.D4) σ φ * fieldActor σ σ =
      fieldActor σ σ * fieldActor σ φ := fun φ => by
    rw [← fieldActor_mul (t := TwistTag.D4), ← fieldActor_mul (t := TwistTag.D4),
      (commute_ringEquiv_of_finite φ σ).eq]
  have hδ₀3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
    have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
    have hσ3' : σ ^ 3 = 1 := RingEquiv.ext fun c => by
      simpa [pow_succ, RingAut.mul_apply] using hσ3 c
    rw [hσ3', map_one] at h
    exact h.symm
  obtain ⟨⟨g, φ⟩, hgφ, -⟩ := existsUnique_conj_mul_fieldActor_D4 hℓ hf hK σ hσ ζ
  have hζ : ζ = MulAut.conj g * fieldActor (t := TwistTag.D4) σ φ := hgφ
  have hgJ : (g : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ σ := by
    have hβδ : fieldActor (t := TwistTag.D4) σ σ * ζ = ζ * fieldActor σ σ := hcomm.symm
    rw [hζ] at hβδ
    have e1 : MulAut.conj (fieldActor (t := TwistTag.D4) σ σ g) *
        (fieldActor σ σ * fieldActor σ φ) =
          MulAut.conj g * (fieldActor σ σ * fieldActor σ φ) := by
      calc MulAut.conj (fieldActor (t := TwistTag.D4) σ σ g) *
          (fieldActor σ σ * fieldActor σ φ) =
          fieldActor σ σ * (MulAut.conj g * fieldActor σ φ) := by
            rw [← mul_assoc, ← mulAut_mul_conj, mul_assoc]
        _ = MulAut.conj g * fieldActor σ φ * fieldActor σ σ := hβδ
        _ = MulAut.conj g * (fieldActor σ σ * fieldActor σ φ) := by rw [mul_assoc, hcommδ]
    exact (d4_mem_trialityFieldImage_self_iff σ hσ3 g).2 (hinj (mul_right_cancel e1))
  have hfixJ : ∀ j : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (j : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ σ → ζ j = j := fun j hj =>
    hfix j ((d4_mem_trialityFieldImage_self_iff σ hσ3 j).1 hj)
  obtain ⟨g', hg', hgg'⟩ := hgJ
  have hid : MulAut.conj (⟨g', hg'⟩ : graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom) *
        fieldActor (fixSubfieldRestrict σ σ) (fixSubfieldRestrict φ σ) = 1 := by
    refine MulEquiv.ext fun j' => Subtype.ext ?_
    have hj'J : baseChangeGL (fixSubfield σ).subtype (j' : ModGL TwistTag.D4.tag
        (fixSubfield σ)) ∈ trialityFieldImage σ σ := ⟨j', j'.2, rfl⟩
    have h1 := congrArg Subtype.val (hfixJ ⟨_, hJC hj'J⟩ hj'J)
    rw [hζ] at h1
    change (g : ModGL TwistTag.D4.tag K) * Units.map (entrywiseHom φ.toRingHom)
      (baseChangeGL (fixSubfield σ).subtype (j' : ModGL TwistTag.D4.tag (fixSubfield σ))) *
        (g : ModGL TwistTag.D4.tag K)⁻¹ =
      baseChangeGL (fixSubfield σ).subtype (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) at h1
    rw [← hgg', entrywise_baseChangeGL_fixSubfieldRestrict, ← map_inv, ← map_mul,
      ← map_mul] at h1
    exact hιinj h1
  obtain ⟨hg1, hψ1⟩ := conj_mul_fieldActor_injective_D4 (fixSubfieldRestrict σ σ) hσ₀3
    (g' := 1) (δ' := 1) (by rw [hid, map_one, fieldActor_one, one_mul])
  have hg1' : g = 1 := Subtype.ext (by
    rw [← hgg', show g' = 1 from congrArg Subtype.val hg1, map_one]
    rfl)
  have hφσ : ∀ x, σ x = x → φ x = x := fun x hx => by
    have h2 := congrArg (fun ψ : fixSubfield σ ≃+* fixSubfield σ => (ψ ⟨x, hx⟩ : K)) hψ1
    exact h2
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1
    (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hφσ)
  have hζn : ζ = fieldActor (t := TwistTag.D4) σ σ ^ n := by
    rw [hζ, hg1', map_one, one_mul]
    exact map_zpow (fieldActorHom (t := TwistTag.D4) σ) σ n
  have hζ3 : ζ ^ 3 = 1 := by
    rw [hζn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hδ₀3, one_zpow]
  have hdvd : orderOf ζ ∣ 3 := orderOf_dvd_of_pow_eq_one hζ3
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm hdvd)

theorem normal_eq_bot_of_coprime_three_graphFixedRootGroup_id {k : Type} [Field k] [Finite k]
    (hk3 : ¬ 3 ∣ Nat.card k) (τ : k ≃+* k) (hτ : τ.toRingHom = RingHom.id k)
    (M : Subgroup (graphFixedRootGroup TwistTag.D4 k τ.toRingHom)) [M.Normal]
    (hM : Nat.Coprime 3 (Nat.card M)) : M = ⊥ := by
  classical
  have := finite_modGL (τ := TwistTag.D4.tag) (K := k)
  rcases fixed_normal_Borel_saturation TwistTag.D4 k τ M with hZ | hsat
  · rw [exceptional_fixed_center_trivial TwistTag.D4 k τ] at hZ
    exact le_bot_iff.1 hZ
  exfalso
  have hBC := graphFixedRootBorel_le TwistTag.D4 k τ.toRingHom
  let fB : graphFixedRootBorel TwistTag.D4 k τ.toRingHom →*
      graphFixedRootGroup TwistTag.D4 k τ.toRingHom ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion hBC)
  have hfB : Function.Surjective fB := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have hx : (x : ModGL TwistTag.D4.tag k) ∈
        ((M.map (graphFixedRootGroup TwistTag.D4 k τ.toRingHom).subtype :
            Set (ModGL TwistTag.D4.tag k)) *
          (graphFixedRootBorel TwistTag.D4 k τ.toRingHom : Set (ModGL TwistTag.D4.tag k))) := by
      rw [hsat.1, hsat.2]
      exact x.2
    obtain ⟨_, ⟨m, hm, rfl⟩, b, hb, hmb⟩ := hx
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk (Subgroup.inclusion hBC ⟨b, hb⟩) :
      graphFixedRootGroup TwistTag.D4 k τ.toRingHom ⧸ M) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    have e : (Subgroup.inclusion hBC ⟨b, hb⟩)⁻¹ * x = (Subgroup.inclusion hBC ⟨b, hb⟩)⁻¹ * m *
        Subgroup.inclusion hBC ⟨b, hb⟩ := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, ← hmb]
      rfl
    rw [e]
    have h := Subgroup.Normal.conj_mem inferInstance m hm (Subgroup.inclusion hBC ⟨b, hb⟩)⁻¹
    rwa [inv_inv] at h
  have hdvd : Nat.card (graphFixedRootGroup TwistTag.D4 k τ.toRingHom) ∣
      Nat.card (graphFixedRootBorel TwistTag.D4 k τ.toRingHom) * Nat.card M := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup M]
    exact Nat.mul_dvd_mul_right (Subgroup.card_dvd_of_surjective hfB) _
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  have hC : Nat.card (graphFixedRootGroup TwistTag.D4 k τ.toRingHom) =
      Nat.card k ^ 6 * (Nat.card k ^ 6 - 1) * (Nat.card k ^ 2 - 1) := by
    rw [hτ]
    exact CFSG.HardMathSupport.Lang.Triality.card_graphFixedRootGroup_D4_id
  have hB : Nat.card (graphFixedRootBorel TwistTag.D4 k τ.toRingHom) =
      (Nat.card k - 1) ^ 2 * Nat.card k ^ 6 := by
    rw [hτ, CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootBorel Function.surjective_id,
      CFSG.Timmesfeld.ExceptionalOrders.graphFixedRootTorus_eq_compatTorus
        Function.surjective_id,
      CFSG.HardMathSupport.Lang.Triality.card_compatTorus_D4_id,
      CFSG.HardMathSupport.Lang.Triality.card_graphFixedPosUnipotent_const Function.surjective_id
        (CFSG.HardMathSupport.Lang.Triality.card_orbitField_id TwistTag.D4),
      CFSG.HardMathSupport.Lang.Triality.orbitsIn_pos_D4]
  rw [hC, hB] at hdvd
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Nat.card k = r + 1 := ⟨Nat.card k - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  rw [hr] at hdvd hk3
  have h6 : (r + 1) ^ 6 - 1 = r * ((r + 1) ^ 5 + (r + 1) ^ 4 + (r + 1) ^ 3 + (r + 1) ^ 2 +
      (r + 1) + 1) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [h6, h2, Nat.add_sub_cancel] at hdvd
  have hpos : 0 < r ^ 2 * (r + 1) ^ 6 := by positivity
  have hdvd' : ((r + 1) ^ 5 + (r + 1) ^ 4 + (r + 1) ^ 3 + (r + 1) ^ 2 + (r + 1) + 1) *
      (r + 2) ∣ Nat.card M := by
    refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
    have e1 : (r + 1) ^ 6 * (r * ((r + 1) ^ 5 + (r + 1) ^ 4 + (r + 1) ^ 3 + (r + 1) ^ 2 +
        (r + 1) + 1)) * (r * (r + 2)) = r ^ 2 * (r + 1) ^ 6 * (((r + 1) ^ 5 + (r + 1) ^ 4 +
          (r + 1) ^ 3 + (r + 1) ^ 2 + (r + 1) + 1) * (r + 2)) := by ring
    have e2 : r ^ 2 * (r + 1) ^ 6 * Nat.card M = r ^ 2 * (r + 1) ^ 6 * Nat.card M := rfl
    rw [e1] at hdvd
    exact hdvd
  have h3 : 3 ∣ ((r + 1) ^ 5 + (r + 1) ^ 4 + (r + 1) ^ 3 + (r + 1) ^ 2 + (r + 1) + 1) *
      (r + 2) := by
    have hr3 : r % 3 = 0 ∨ r % 3 = 1 := by omega
    rcases hr3 with h | h
    · refine Dvd.dvd.mul_right ?_ _
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.pow_mod, h]
    · refine Dvd.dvd.mul_left ?_ _
      omega
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hM (h3.trans hdvd')

theorem fixSub_fieldActor_self_normal_eq_bot {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hNT : N ≤ fixSub (fieldActor (t := TwistTag.D4) σ σ))
    (hNn : ∀ g ∈ fixSub (fieldActor (t := TwistTag.D4) σ σ), ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  classical
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  set T := fixSub (fieldActor (t := TwistTag.D4) σ σ) with hT
  have hιinj : Function.Injective
      (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype) := baseChangeGL_injective _
  let e : ↥T ≃* ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom) :=
    ((Subgroup.equivMapOfInjective T (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (map_fixSub_fieldActor_self σ hσ3))).trans
      (Subgroup.equivMapOfInjective _ _ hιinj).symm
  have hN1 : (N.subgroupOf T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn _ g.2 _ hn
  have hMn : ((N.subgroupOf T).map e.toMonoidHom).Normal := hN1.map _ e.surjective
  have hcardM : Nat.card ((N.subgroupOf T).map e.toMonoidHom) = Nat.card N := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv
  have hk : Nat.card (fixSubfield σ) = ℓ ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hℓ hf hK σ hσ
  have hk3 : ¬ 3 ∣ Nat.card (fixSubfield σ) := by
    rw [hk]
    exact fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hσ₀ : (fixSubfieldRestrict σ σ).toRingHom = RingHom.id (fixSubfield σ) :=
    RingHom.ext fun c => Subtype.ext (by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_fixSubfieldRestrict]
      exact c.2)
  have hM := normal_eq_bot_of_coprime_three_graphFixedRootGroup_id hk3 (fixSubfieldRestrict σ σ)
    hσ₀ ((N.subgroupOf T).map e.toMonoidHom) (by rw [hcardM]; exact hcop)
  refine eq_bot_iff.2 fun n hn => ?_
  have hmem : e ⟨n, hNT hn⟩ ∈ (N.subgroupOf T).map e.toMonoidHom :=
    ⟨⟨n, hNT hn⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
  rw [hM, Subgroup.mem_bot, map_eq_one_iff _ e.injective] at hmem
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val hmem)

theorem coreFreeAt_three_fieldActor_self {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) : CoreFreeAt 3 (fieldActor (t := TwistTag.D4) σ σ) :=
  ⟨fixSub_fieldActor_self_normal_eq_bot hℓ hℓ3 hf hK σ hσ,
    fun g hg hgx hfix => eq_one_of_fix_fixSub_fieldActor_self hℓ hf hK σ hσ g hg hgx hfix⟩

end G2Class

end CFSG.HardMathSupport.Timmesfeld.CrossChar
