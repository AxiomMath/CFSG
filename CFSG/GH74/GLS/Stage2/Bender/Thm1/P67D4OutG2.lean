module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutTorus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem d4_mem_twistedFixedGroup_id_iff' {K : Type} [Field K] {g : ModGL TwistTag.D4.tag K} :
    g ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K) ↔
      g ∈ adjointGroup TwistTag.D4.tag K ∧
        diagramMap TwistTag.D4 K * g = g * diagramMap TwistTag.D4 K := by
  have hid : Units.map (entrywiseHom (RingHom.id K)) g = g := Units.ext (entrywise_id _)
  constructor
  · intro hg
    refine ⟨hg.1, ?_⟩
    have h := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K (RingHom.id K)).1 hg).2
    rw [twistHom_apply, hid] at h
    calc diagramMap TwistTag.D4 K * g =
        diagramMap TwistTag.D4 K * g * (diagramMap TwistTag.D4 K)⁻¹ *
          diagramMap TwistTag.D4 K := by group
      _ = g * diagramMap TwistTag.D4 K := by rw [h]
  · rintro ⟨hC, hP⟩
    refine ⟨hC, ?_⟩
    change twistHom TwistTag.D4 K (RingHom.id K) g = g
    rw [twistHom_apply, hid, hP, mul_inv_cancel_right]

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section G2Class

variable {K : Type} [Field K] [Finite K]

theorem d4_mem_trialityFieldImage_self_iff (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    (g : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ σ ↔ fieldActor σ σ g = g := by
  constructor
  · rintro ⟨g', -, hg'⟩
    refine Subtype.ext ?_
    rw [coe_fieldActor, ← hg']
    have hcomp : σ.toRingHom.comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
      RingHom.ext fun x => x.2
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]
  · intro hfix
    have hgΓ := graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom g.2
    have hP := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hgΓ).2
    have hfixU : Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K) = g := by
      rw [← coe_fieldActor, hfix]
    have hE : (g : ModGL TwistTag.D4.tag K) ∈ entrywiseFixedGroup TwistTag.D4.tag σ :=
      ⟨hgΓ.1, hfixU⟩
    rw [entrywiseFixedGroup_D4_eq_fixedFieldImage_of_cube σ hσ3] at hE
    obtain ⟨g', hg', hgg'⟩ := hE
    rw [twistHom_apply, hfixU] at hP
    have hg'P : diagramMap TwistTag.D4 (fixSubfield σ) * g' =
        g' * diagramMap TwistTag.D4 (fixSubfield σ) := by
      apply baseChangeGL_injective (fixSubfield σ).subtype
      rw [map_mul, map_mul, baseChangeGL_diagramMap, hgg']
      calc diagramMap TwistTag.D4 K * (g : ModGL TwistTag.D4.tag K) =
          diagramMap TwistTag.D4 K * g * (diagramMap TwistTag.D4 K)⁻¹ *
            diagramMap TwistTag.D4 K := by group
        _ = g * diagramMap TwistTag.D4 K := by rw [hP]
    have hg'Γ := (d4_mem_twistedFixedGroup_id_iff' (K := fixSubfield σ)).2 ⟨hg', hg'P⟩
    have hσ₀ : (fixSubfieldRestrict σ σ).toRingHom = RingHom.id (fixSubfield σ) :=
      RingHom.ext fun c => Subtype.ext (by
        rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_fixSubfieldRestrict]
        exact c.2)
    have hid3 : ∀ c : fixSubfield σ, (RingEquiv.refl (fixSubfield σ)) ((RingEquiv.refl
        (fixSubfield σ)) ((RingEquiv.refl (fixSubfield σ)) c)) = c := fun _ => rfl
    have htw := twistedFixedGroup_eq_graphFixedRootGroup_triality (K := fixSubfield σ)
      (RingEquiv.refl (fixSubfield σ)) hid3 (Or.inr ⟨1, odd_one, fun c => (pow_one c).symm⟩)
    have hrefl : (RingEquiv.refl (fixSubfield σ)).toRingHom = RingHom.id (fixSubfield σ) := rfl
    rw [hrefl] at htw
    refine ⟨g', ?_, hgg'⟩
    rw [hσ₀, ← htw]
    exact hg'Γ

theorem d4_trialityFieldImage_self_simple {p : ℕ} [CharP K p] (hp2 : p ≠ 2) (σ : K ≃+* K) :
    IsSimpleGroup (trialityFieldImage σ σ) ∧
      ¬∀ a b : trialityFieldImage σ σ, a * b = b * a := by
  have hk : ringChar (fixSubfield σ) ≠ 2 := by
    have : CharP (fixSubfield σ) p := inferInstance
    rw [ringChar.eq (fixSubfield σ) p]
    exact hp2
  obtain ⟨h1, ⟨x, y, hxy⟩, -⟩ :=
    odd_diagram_field_fixed_p_components TwistTag.D4 (fixSubfield σ) hk (fixSubfieldRestrict σ σ)
  have hιinj : Function.Injective
      (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype) := baseChangeGL_injective _
  set e := Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
    (fixSubfieldRestrict σ σ).toRingHom) _ hιinj with he
  refine ⟨e.symm.isSimpleGroup, fun h => hxy ?_⟩
  apply e.injective
  rw [map_mul, map_mul]
  exact h _ _

theorem d4_trialityFieldImage_self_le (σ : K ≃+* K) :
    trialityFieldImage σ σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  map_baseChangeGL_graphFixedRootGroup_le (σ := (fixSubfieldRestrict σ σ).toRingHom)
    (Fr := σ.toRingHom) (ι := (fixSubfield σ).subtype) (fixSubfieldRestrict σ σ).surjective
    fun _ => rfl

theorem d4NoAbel_fieldActor {p : ℕ} [CharP K p] (hp2 : p ≠ 2) (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) : D4NoAbel (fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  obtain ⟨hsimple, hnc⟩ := d4_trialityFieldImage_self_simple (K := K) hp2 σ
  have hJC := d4_trialityFieldImage_self_le σ
  have hFJ : (fixSub (fieldActor (t := TwistTag.D4) σ σ)).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = trialityFieldImage σ σ := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (d4_mem_trialityFieldImage_self_iff σ hσ3 g).2 hg
    · intro hx
      exact ⟨⟨x, hJC hx⟩, (d4_mem_trialityFieldImage_self_iff σ hσ3 _).1 hx, rfl⟩
  let e : ↥(fixSub (fieldActor (t := TwistTag.D4) σ σ)) ≃* ↥(trialityFieldImage σ σ) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      Subtype.val_injective).trans (MulEquiv.subgroupCongr hFJ)
  refine noAbelNormal_of_equiv e ?_
  intro N hN hc
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    apply hnc
    intro a b
    have ha : a ∈ N := h ▸ Subgroup.mem_top a
    have hb : b ∈ N := h ▸ Subgroup.mem_top b
    exact congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)

theorem d4PtKer_fieldActor {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    D4PtKer (fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : Fact p.Prime := ⟨hp⟩
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hσ₀3 : ∀ c : fixSubfield σ, fixSubfieldRestrict σ σ (fixSubfieldRestrict σ σ
      (fixSubfieldRestrict σ σ c)) = c := fun c => Subtype.ext (by
    simp only [coe_fixSubfieldRestrict]
    exact hσ3 c)
  obtain ⟨-, hNF, -⟩ := odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
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
  intro ζ _ hcop hcomm hfix
  obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF ζ
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
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

end G2Class

theorem d4OuterThreeG2_thm : D4OuterThreeG2 := by
  intro p f hp hp2 hp3 hf K _ _ hK σ hσ
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  exact ⟨d4NoAbel_fieldActor hp2 σ (ringEquiv_cube_apply_eq hK hσ),
    d4PtKer_fieldActor hp hp2 hf hK σ hσ⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
