module

public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem entrywise_baseChangeGL_fixSubfieldRestrict
    {τ : Tag} {K : Type} [Field K] [Finite K]
    (φ δ : K ≃+* K) (j : ModGL τ (fixSubfield δ)) :
    Units.map (entrywiseHom φ.toRingHom) (baseChangeGL (fixSubfield δ).subtype j) =
      baseChangeGL (fixSubfield δ).subtype
        (Units.map (entrywiseHom (fixSubfieldRestrict φ δ).toRingHom) j) := by
  change baseChangeGL φ.toRingHom (baseChangeGL (fixSubfield δ).subtype j) =
    baseChangeGL (fixSubfield δ).subtype (baseChangeGL (fixSubfieldRestrict φ δ).toRingHom j)
  rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL]
  rfl

theorem conj_mul_fieldActor_injective_D4
    {L : Type} [Field L] [Finite L] (τ : L ≃+* L)
    (hτ3 : ∀ c, τ (τ (τ c)) = c) {g g' : graphFixedRootGroup TwistTag.D4 L τ.toRingHom}
    {δ δ' : L ≃+* L}
    (h : MulAut.conj g * fieldActor τ δ = MulAut.conj g' * fieldActor τ δ') :
    g = g' ∧ δ = δ' := by
  have h0 := orbitField_D4_zero_eq_top τ hτ3
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 L τ
  have e : fieldActor τ δ' * (fieldActor τ δ)⁻¹ = MulAut.conj (g'⁻¹ * g) := by
    have h' : fieldActor τ δ' = (MulAut.conj g')⁻¹ * MulAut.conj g * fieldActor τ δ := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h', mul_inv_cancel_right, map_mul, map_inv]
  have hEmem : ∀ ε : L ≃+* L,
      fieldActor τ ε ∈ graphFixedUnipotentStabilizer TwistTag.D4 L τ.toRingHom := fun ε => by
    have := normalActor_mem (t := TwistTag.D4) τ 1 ε
    rwa [normalActor_one_left] at this
  have hA : MulAut.conj (g'⁻¹ * g) ∈
      graphFixedUnipotentStabilizer TwistTag.D4 L τ.toRingHom := by
    rw [← e]
    exact mul_mem (hEmem δ') (inv_mem (hEmem δ))
  obtain ⟨w, hw⟩ := exists_conj_eq_compatDiagAutHom τ.surjective hA
  have e2 : normalActor τ w δ = normalActor τ 1 δ' := by
    rw [normalActor_one_left, normalActor, ← hw, ← e, inv_mul_cancel_right]
  have hδ := eq_of_normalActor_eq_D4 h0 e2
  subst hδ
  refine ⟨?_, rfl⟩
  have hw1 : compatDiagAutHom TwistTag.D4 L τ.toRingHom w = 1 := by
    have e3 : compatDiagAutHom TwistTag.D4 L τ.toRingHom w * fieldActor τ δ =
        1 * fieldActor τ δ := by
      rw [one_mul]
      change normalActor τ w δ = _
      rw [e2, normalActor_one_left]
    exact mul_right_cancel e3
  have h1 : MulAut.conj (g'⁻¹ * g) = 1 := hw.trans hw1
  have h2 := mulAut_conj_injective_of_center_eq_bot hZ (h1.trans (map_one _).symm)
  exact (inv_mul_eq_one.1 h2).symm

theorem triality_field_facts
    {e : ℕ} (he : 1 ≤ e) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (6 * e)) {σ δ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ (2 * e))
    (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e)) :
    σ ^ 3 = 1 ∧ δ ^ 2 = 1 ∧ δ ≠ 1 ∧ Nat.card (fixSubfield δ) = 2 ^ (3 * e) ∧
      orderOf (fixSubfieldRestrict σ δ) = 3 := by
  obtain ⟨φ, hφ, hord, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 6 * e) hK
  have hσφ : σ = φ ^ (2 * e) := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hφ]
  have hδφ : δ = φ ^ (3 * e) := RingEquiv.ext fun c => by
    rw [hδ, ringAut_pow_apply_of_frobenius hφ]
  have hφ6 : φ ^ (6 * e) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one φ
  have hσ3 : σ ^ 3 = 1 := by rw [hσφ, ← pow_mul, show 2 * e * 3 = 6 * e by ring, hφ6]
  have hδ2 : δ ^ 2 = 1 := by rw [hδφ, ← pow_mul, show 3 * e * 2 = 6 * e by ring, hφ6]
  have hne : ∀ m, 0 < m → m < 6 * e → φ ^ m ≠ 1 := fun m hm hm6 h1 => by
    have := Nat.le_of_dvd hm (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  have hδ1 : δ ≠ 1 := by
    rw [hδφ]
    exact hne _ (by omega) (by omega)
  have hσ1 : σ ≠ 1 := by
    rw [hσφ]
    exact hne _ (by omega) (by omega)
  obtain ⟨-, -, hcard⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two (by omega) hK hδ2 hδ1
  have hk : Nat.card (fixSubfield δ) = 2 ^ (3 * e) := by
    rw [show 6 * e / 2 = 3 * e by omega] at hcard
    exact hcard
  have h03 : fixSubfieldRestrict σ δ ^ 3 = 1 := fixSubfieldRestrict_pow_eq_one δ hσ3
  have h01 : fixSubfieldRestrict σ δ ≠ 1 := by
    intro h1
    have hfix : ∀ x, δ x = x → σ x = x := fun x hx => by
      have h2 := congrArg (fun ψ : fixSubfield δ ≃+* fixSubfield δ => (ψ ⟨x, hx⟩ : K)) h1
      exact h2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
      (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hfix)
    have hσ2 : σ ^ 2 = 1 := by
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hδ2, one_zpow]
    apply hσ1
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hσ3, hσ2, inv_one, one_mul]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨hσ3, hδ2, hδ1, hk, orderOf_eq_prime h03 h01⟩

section Data

variable {K : Type} [Field K] [Finite K]

@[expose] def trialityFieldImage
    (σ δ : K ≃+* K) : Subgroup (ModGL TwistTag.D4.tag K) :=
  (graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
    (baseChangeGL (fixSubfield δ).subtype)

@[expose] def trialityFieldInner
    (σ δ : K ≃+* K) :
    Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
  ((trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
    MulAut.conj

end Data


theorem even_triality_canonical_field_full_centralizer
    {e : ℕ} (he : 1 ≤ e) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (6 * e)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ (2 * e)) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e)) :
    (∀ c : K, c ∈ fixSubfield δ ↔ c ^ 2 ^ (3 * e) = c) ∧
      Nat.card (fixSubfield δ) = 2 ^ (3 * e) ∧
      (∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ c : K) = σ c) ∧
      orderOf (fixSubfieldRestrict σ δ) = 3 ∧
      trialityFieldImage σ δ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      ((fieldActor σ δ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = trialityFieldImage σ δ ∧
      (∃ ι : ↥((trialityFieldImage σ δ).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃* ↥(trialityFieldInner σ δ),
        ∀ j, (ι j : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
          MulAut.conj (j : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
      (∀ β ∈ Subgroup.centralizer {fieldActor σ δ},
        ∃! gφ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom × (K ≃+* K),
          (gφ.1 : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ ∧
            β = MulAut.conj gφ.1 * fieldActor σ gφ.2) ∧
      trialityFieldInner σ δ ≤ Subgroup.centralizer {fieldActor σ δ} ∧
      ((trialityFieldInner σ δ).subgroupOf (Subgroup.centralizer {fieldActor σ δ})).Normal ∧
      Subgroup.centralizer {fieldActor σ δ} ⊓
          Subgroup.centralizer (trialityFieldInner σ δ :
            Set (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) =
        Subgroup.zpowers (fieldActor σ δ) := by
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hcharK : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hσ3, -, -, hk, hord⟩ := triality_field_facts he hK hσ hδ
  have : Finite (fixSubfield δ) := Subtype.finite
  have hσ₀3 : ∀ c, fixSubfieldRestrict σ δ (fixSubfieldRestrict σ δ
      (fixSubfieldRestrict σ δ c)) = c := fun c => by
    have h := congrArg (fun ψ : fixSubfield δ ≃+* fixSubfield δ => ψ c)
      (pow_orderOf_eq_one (fixSubfieldRestrict σ δ))
    rw [hord] at h
    exact h
  have hσ3pt : ∀ c, σ (σ (σ c)) = c := fun c => congrArg (fun ψ : K ≃+* K => ψ c) hσ3
  have : CharP (fixSubfield δ) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 3 * e) hk
  have hcharK₀ : ringChar (fixSubfield δ) = 2 := ringChar.eq (fixSubfield δ) 2
  obtain ⟨hΓK, -⟩ := even_triality_fixed_group_eq_root_group K hcharK σ hσ3pt
  obtain ⟨hΓK₀, -⟩ := even_triality_fixed_group_eq_root_group (fixSubfield δ) hcharK₀
    (fixSubfieldRestrict σ δ) hσ₀3
  have hXJ : entrywiseFixedGroup TwistTag.D4.tag δ = fixedFieldImage TwistTag.D4.tag δ := by
    obtain ⟨-, -, -, hJΓ, hΓ, -⟩ :=
      Chevalley_coordinate_field_fixed_normal_subgroup TwistTag.D4.tag K δ
    have hT := (even_power_two_Cartan_root_diagonals_inner TwistTag.D4.tag
      (Or.inr (Or.inr (Or.inl rfl))) K hcharK).2.2.2 δ
    refine le_antisymm (fun g hg => ?_) hJΓ
    have hg' : g ∈ (entrywiseFixedGroup TwistTag.D4.tag δ : Set (ModGL TwistTag.D4.tag K)) := hg
    rw [hΓ] at hg'
    obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
    refine mul_mem ?_ hj
    have hh' : h ∈ torusGroup TwistTag.D4.tag K ⊓
        (Units.map (entrywiseHom δ.toRingHom)).eqLocus (MonoidHom.id _) := ⟨hh.1, hh.2.2⟩
    rw [hT] at hh'
    obtain ⟨t, ht, rfl⟩ := hh'
    have hle : torusGroup TwistTag.D4.tag (fixSubfield δ) ≤
        adjointGroup TwistTag.D4.tag (fixSubfield δ) :=
      (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
    exact ⟨t, hle ht, rfl⟩
  have hJeq : trialityFieldImage σ δ = C ⊓ entrywiseFixedGroup TwistTag.D4.tag δ := by
    rw [trialityFieldImage, ← hΓK₀,
      map_baseChangeGL_twistedFixedGroup_eq (coe_fixSubfieldRestrict σ δ), hΓK, ← hXJ]
    exact inf_of_le_right inf_le_right
  have hJC : trialityFieldImage σ δ ≤ C := by
    rw [hJeq]
    exact inf_le_left
  have hCadj : C ≤ adjointGroup TwistTag.D4.tag K := fun g hg =>
    twistedFixedGroup_le_adjointGroup _ _ _ (graphFixedRootGroup_le _ _ _ hg)
  have hmemJ : ∀ g : C, (g : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ ↔
      fieldActor σ δ g = g := by
    intro g
    rw [hJeq, Subgroup.mem_inf, mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, -, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, hCadj g.2, congrArg Subtype.val h⟩
  have hK' : Nat.card K = (2 ^ (2 * e)) ^ 3 := by rw [hK, ← pow_mul]; ring_nf
  obtain ⟨-, hNF, -⟩ := even_triality_exact_automorphism_normal_form (f := 2 * e) (by omega) K hK'
    σ hσ
  have hZ : Subgroup.center C = ⊥ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hcommδ : ∀ φ : K ≃+* K, fieldActor σ φ * fieldActor σ δ =
      fieldActor σ δ * fieldActor σ φ := fun φ => by
    rw [← fieldActor_mul (t := TwistTag.D4), ← fieldActor_mul (t := TwistTag.D4),
      (commute_ringEquiv_of_finite φ δ).eq]
  have hcentJ : ∀ β ∈ Subgroup.centralizer {fieldActor σ δ}, ∀ (g : C) (φ : K ≃+* K),
      β = MulAut.conj g * fieldActor σ φ →
        (g : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ := by
    intro β hβ g φ h
    have hβδ : fieldActor σ δ * β = β * fieldActor σ δ :=
      Subgroup.mem_centralizer_iff.1 hβ _ (Set.mem_singleton _)
    rw [h] at hβδ
    have e1 : MulAut.conj (fieldActor σ δ g) * (fieldActor σ δ * fieldActor σ φ) =
        MulAut.conj g * (fieldActor σ δ * fieldActor σ φ) := by
      calc MulAut.conj (fieldActor σ δ g) * (fieldActor σ δ * fieldActor σ φ) =
          fieldActor σ δ * (MulAut.conj g * fieldActor σ φ) := by
            rw [← mul_assoc, ← mulAut_mul_conj, mul_assoc]
        _ = MulAut.conj g * fieldActor σ φ * fieldActor σ δ := hβδ
        _ = MulAut.conj g * (fieldActor σ δ * fieldActor σ φ) := by rw [mul_assoc, hcommδ]
    exact (hmemJ g).2 (hinj (mul_right_cancel e1))
  have hNδ : trialityFieldInner σ δ ≤ Subgroup.centralizer {fieldActor σ δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
  refine ⟨fun c => by rw [mem_fixSubfield, hδ], hk, coe_fixSubfieldRestrict σ δ, hord, hJC, ?_,
    ⟨((trialityFieldImage σ δ).subgroupOf C).equivMapOfInjective _ hinj, fun j => rfl⟩,
    fun β hβ => ?_, hNδ, ⟨fun n hn g => ?_⟩, le_antisymm (fun β hβ => ?_) ?_⟩
  ·
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hmemJ g).2 hg
    · intro hx
      exact ⟨⟨x, hJC hx⟩, (hmemJ _).1 hx, rfl⟩
  ·
    obtain ⟨⟨g, φ⟩, hgφ, huniq⟩ := hNF β
    exact ⟨(g, φ), ⟨hcentJ β hβ g φ hgφ, hgφ⟩, fun q hq => huniq q hq.2⟩
  ·
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_subgroupOf.1 hn
    rw [SetLike.mem_coe] at hj
    have hgδ : fieldActor σ δ * (g : MulAut C) = (g : MulAut C) * fieldActor σ δ :=
      Subgroup.mem_centralizer_iff.1 g.2 _ (Set.mem_singleton _)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut C) j, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc fieldActor σ δ ((g : MulAut C) j) =
            (fieldActor σ δ * (g : MulAut C) : MulAut C) j := rfl
        _ = ((g : MulAut C) * fieldActor σ δ : MulAut C) j := by rw [hgδ]
        _ = (g : MulAut C) (fieldActor σ δ j) := rfl
        _ = (g : MulAut C) j := by rw [(hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  ·
    obtain ⟨hβδ, hβN⟩ := Subgroup.mem_inf.1 hβ
    obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF β
    have hgJ := hcentJ β hβδ g φ hgφ
    have hfix : ∀ j : C, (j : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ → β j = j := by
      intro j hj
      have hn : MulAut.conj j ∈ trialityFieldInner σ δ :=
        ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      have h1 : MulAut.conj j * β = β * MulAut.conj j :=
        Subgroup.mem_centralizer_iff.1 hβN _ hn
      have h2 : MulAut.conj (β j) = MulAut.conj j := by
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      exact hinj h2
    obtain ⟨g', hg', hgg'⟩ := hgJ
    have hιinj : Function.Injective (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δ).subtype) :=
      baseChangeGL_injective _
    have hid : MulAut.conj (⟨g', hg'⟩ : graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom) *
          fieldActor (fixSubfieldRestrict σ δ) (fixSubfieldRestrict φ δ) = 1 := by
      refine MulEquiv.ext fun j' => Subtype.ext ?_
      have hj'J : baseChangeGL (fixSubfield δ).subtype (j' : ModGL TwistTag.D4.tag
          (fixSubfield δ)) ∈ trialityFieldImage σ δ := ⟨j', j'.2, rfl⟩
      have h1 := congrArg Subtype.val (hfix ⟨_, hJC hj'J⟩ hj'J)
      rw [hgφ] at h1
      change (g : ModGL TwistTag.D4.tag K) * Units.map (entrywiseHom φ.toRingHom)
        (baseChangeGL (fixSubfield δ).subtype (j' : ModGL TwistTag.D4.tag (fixSubfield δ))) *
          (g : ModGL TwistTag.D4.tag K)⁻¹ =
        baseChangeGL (fixSubfield δ).subtype (j' : ModGL TwistTag.D4.tag (fixSubfield δ)) at h1
      rw [← hgg', entrywise_baseChangeGL_fixSubfieldRestrict, ← map_inv, ← map_mul,
        ← map_mul] at h1
      exact hιinj h1
    obtain ⟨hg1, hψ1⟩ := conj_mul_fieldActor_injective_D4 (fixSubfieldRestrict σ δ) hσ₀3
      (g' := 1) (δ' := 1) (by rw [hid, map_one, fieldActor_one, one_mul])
    have hg1' : g = 1 := Subtype.ext (by
      rw [← hgg', show g' = 1 from congrArg Subtype.val hg1, map_one]
      rfl)
    have hφK₀ : ∀ x, δ x = x → φ x = x := fun x hx => by
      have h2 := congrArg (fun ψ : fixSubfield δ ≃+* fixSubfield δ => (ψ ⟨x, hx⟩ : K)) hψ1
      exact h2
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1
      (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hφK₀)
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hgφ, hg1', map_one, one_mul]
    exact (map_zpow (fieldActorHom (t := TwistTag.D4) σ) δ n).symm
  ·
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) _ (Set.mem_singleton _)).symm⟩)

end CFSG.LieType.Chevalley
