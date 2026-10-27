module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcEField

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank

theorem pow_pow_eq_self_of_pow_eq_self {M : Type*} [Monoid M] {c : M} {N : ℕ}
    (h : c ^ N = c) (k : ℕ) : c ^ (N ^ k) = c := by
  induction k with
  | zero => rw [pow_zero, pow_one]
  | succ k ih => rw [pow_succ, pow_mul, ih, h]

theorem card_fixSubfield_of_odd_orderOf {K : Type} [Field K] {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hK : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    (φ : K ≃+* K) (hφ : Odd (orderOf φ)) :
    ∃ e' : ℕ, 1 ≤ e' ∧ Nat.card (fixSubfield φ) = (p ^ e') ^ 2 ∧
      ∀ c : K, φ c = c → δ c = c ^ (p ^ e') := by
  have hK' : Nat.card K = p ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK']; exact (pow_pos hp.pos _).ne')
  obtain ⟨-, -, -, -, -, hA⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega) hK'
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers φ)
  rw [Nat.card_zpowers] at hdvd hcard
  obtain ⟨e', he'⟩ : orderOf φ ∣ e :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_left.2 hφ).symm hdvd
  have hm0 : 0 < orderOf φ := hφ.pos
  have he'1 : 1 ≤ e' := by
    rcases Nat.eq_zero_or_pos e' with h | h
    · rw [h, mul_zero] at he'
      omega
    · exact h
  have hSφ : S = fixSubfield φ := by
    refine SetLike.ext' ?_
    rw [hS]
    ext a
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_fixSubfield]
    constructor
    · intro h
      exact h φ (Subgroup.mem_zpowers φ)
    · intro h τ' hτ'
      have hstab : Subgroup.zpowers φ ≤ MulAction.stabilizer (K ≃+* K) a :=
        Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]; exact h)
      have h' := hstab hτ'
      rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h'
  have hcardφ : Nat.card (fixSubfield φ) = (p ^ e') ^ 2 := by
    rw [← hSφ, hcard, he', show 2 * (orderOf φ * e') = orderOf φ * (2 * e') by ring,
      Nat.mul_div_cancel_left _ hm0, mul_comm, pow_mul]
  refine ⟨e', he'1, hcardφ, fun c hc => ?_⟩
  have : Fintype (fixSubfield φ) := Fintype.ofFinite _
  have hc2 : c ^ ((p ^ e') ^ 2) = c := by
    have h1 := FiniteField.pow_card (⟨c, hc⟩ : fixSubfield φ)
    rw [← Nat.card_eq_fintype_card, hcardφ] at h1
    exact (SubmonoidClass.coe_pow _ _).symm.trans (congrArg Subtype.val h1)
  obtain ⟨k, hk⟩ := hφ
  have hpe : p ^ e = ((p ^ e') ^ 2) ^ k * p ^ e' := by
    calc p ^ e = (p ^ e') ^ (2 * k + 1) := by rw [he', hk, mul_comm, pow_mul]
      _ = ((p ^ e') ^ 2) ^ k * p ^ e' := by rw [pow_succ, pow_mul]
  rw [hδ, hpe, pow_mul, pow_pow_eq_self_of_pow_eq_self hc2]

theorem outerCoreTrivAt_graph_field_E6
    {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {β : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hβ : ∀ u, (β u : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
      Units.map (entrywiseHom δ.toRingHom) (u : ModGL TwistTag.E6.tag K) *
        (diagramMap TwistTag.E6 K)⁻¹) : OuterCoreTrivAt β := by
  classical
  have hK' : Nat.card K = p ^ (2 * e) := by rw [hKe, ← pow_mul, mul_comm]
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK'
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hZ : center (adjointGroup TwistTag.E6.tag K) = ⊥ := center_adjointGroup_eq_bot
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hδ2 : δ ^ 2 = 1 := pow_eq_one_of_apply_eq_pow δ hKe hδ
  have hfixΓ : ∀ s : adjointGroup TwistTag.E6.tag K, β s = s ↔
      (s : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K δ.toRingHom := by
    intro s
    constructor
    · intro hs
      refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K δ.toRingHom).2 ⟨s.2, ?_⟩
      rw [twistHom_apply, ← hβ s, hs]
    · intro hs
      have h1 := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K δ.toRingHom).1 hs).2
      rw [twistHom_apply] at h1
      exact Subtype.ext ((hβ s).trans h1)
  have hC₀Γ := graphFixedRootGroup_le TwistTag.E6 K δ.toRingHom
  have hC₀C : graphFixedRootGroup TwistTag.E6 K δ.toRingHom ≤ adjointGroup TwistTag.E6.tag K :=
    hC₀Γ.trans (twistedFixedGroup_le_adjointGroup TwistTag.E6 K δ.toRingHom)
  obtain ⟨hJs0, hJna0, -⟩ := odd_diagram_field_fixed_p_components TwistTag.E6 K hK2 δ
  have eJ : (graphFixedRootGroup TwistTag.E6 K δ.toRingHom).subgroupOf
      (adjointGroup TwistTag.E6.tag K) ≃* graphFixedRootGroup TwistTag.E6 K δ.toRingHom :=
    Subgroup.subgroupOfEquivOfLe hC₀C
  have hJs : IsSimpleGroup ((graphFixedRootGroup TwistTag.E6 K δ.toRingHom).subgroupOf
      (adjointGroup TwistTag.E6.tag K)) := (MulEquiv.isSimpleGroup_congr eJ).2 hJs0
  have hJna : ∃ x y : (graphFixedRootGroup TwistTag.E6 K δ.toRingHom).subgroupOf
      (adjointGroup TwistTag.E6.tag K), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hJna0
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (eJ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hJfix : ∀ j ∈ (graphFixedRootGroup TwistTag.E6 K δ.toRingHom).subgroupOf
      (adjointGroup TwistTag.E6.tag K), β j = j := fun j hj => (hfixΓ j).2 (hC₀Γ hj)
  have hJnorm : ∀ s : adjointGroup TwistTag.E6.tag K, β s = s →
      ∀ j ∈ (graphFixedRootGroup TwistTag.E6 K δ.toRingHom).subgroupOf
        (adjointGroup TwistTag.E6.tag K), s * j * s⁻¹ ∈
          (graphFixedRootGroup TwistTag.E6 K δ.toRingHom).subgroupOf
            (adjointGroup TwistTag.E6.tag K) := by
    intro s hs j hj
    have hsN := twistedFixedGroup_le_normalizer (t := TwistTag.E6) (σ := δ.toRingHom)
      δ.surjective ((hfixΓ s).1 hs)
    exact (Subgroup.mem_normalizer_iff.1 hsN (j : ModGL TwistTag.E6.tag K)).1 hj
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  intro R hRodd hRi hRc r hr
  have hrJ : ∀ j ∈ (graphFixedRootGroup TwistTag.E6 K δ.toRingHom).subgroupOf
      (adjointGroup TwistTag.E6.tag K), r j = j :=
    fun j hj => fix_of_fixed_normal_simple hZ hRodd hRi hRc hJfix hJnorm hJs hJna hr hj
  have hro : Odd (orderOf r) := odd_orderOf_of_mem hRodd hr
  obtain ⟨g, a, φ, ε, hgaφ⟩ := hNF r
  have hΘr : Θ r ^ orderOf r = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [hΘ r g a φ ε hgaφ] at hΘr
  have hε : (ε : ℕ) = 0 := by
    have h2 := congrArg Prod.snd hΘr
    rw [Prod.pow_snd, Prod.snd_one, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h2
    have hε2 : (ε : ℕ) < 2 := ε.isLt
    by_contra hne
    have hε1 : (ε : ℕ) = 1 := by omega
    rw [hε1, Nat.cast_one, mul_one] at h2
    have h3 : ((orderOf r : ℕ) : ZMod 2) = 0 := h2
    exact (Nat.not_even_iff_odd.2 hro) (ZMod.natCast_eq_zero_iff_even.1 h3)
  have hφo : Odd (orderOf φ) := by
    have h2 := congrArg Prod.fst hΘr
    rw [Prod.pow_fst, Prod.fst_one] at h2
    exact Odd.of_dvd_nat hro (orderOf_dvd_of_pow_eq_one h2)
  have hQ : exactQ TwistTag.E6.tag K (ε : ℕ) = 1 := by
    rw [hε]
    exact pow_zero _
  obtain ⟨x, hx⟩ : ∃ x : ModGL TwistTag.E6.tag K,
      x = (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a := ⟨_, rfl⟩
  have hr' : ∀ h : adjointGroup TwistTag.E6.tag K, (r h : ModGL TwistTag.E6.tag K) =
      x * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag K) * x⁻¹ := fun h => by
    rw [hgaφ h, hQ, hx]
    group
  obtain ⟨e', he', hK'card, hδφ⟩ := card_fixSubfield_of_odd_orderOf hp he hKe δ hδ φ hφo
  have : Finite (fixSubfield φ) := Subtype.finite
  have hφK' : φ.toRingHom.comp (fixSubfield φ).subtype = (fixSubfield φ).subtype :=
    RingHom.ext fun c => (mem_fixSubfield φ).1 c.2
  have hδ' : ∀ c : fixSubfield φ, (fixSubfieldRestrict δ φ).toRingHom c = c ^ (p ^ e') :=
    fun c => Subtype.ext ((hδφ (c : K) ((mem_fixSubfield φ).1 c.2)).trans
      (SubmonoidClass.coe_pow c _).symm)
  have hmap : (graphFixedRootGroup TwistTag.E6 (fixSubfield φ)
      (fixSubfieldRestrict δ φ).toRingHom).map (baseChangeGL (fixSubfield φ).subtype) ≤
        graphFixedRootGroup TwistTag.E6 K δ.toRingHom :=
    map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6)
      (σ := (fixSubfieldRestrict δ φ).toRingHom) (Fr := δ.toRingHom)
      (ι := (fixSubfield φ).subtype) (fixSubfieldRestrict δ φ).surjective fun _ => rfl
  have hφfix : ∀ y : ModGL TwistTag.E6.tag (fixSubfield φ),
      Units.map (entrywiseHom φ.toRingHom) (baseChangeGL (fixSubfield φ).subtype y) =
        baseChangeGL (fixSubfield φ).subtype y := fun y => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hφK']
  have hxC : ∀ y ∈ graphFixedRootGroup TwistTag.E6 (fixSubfield φ)
      (fixSubfieldRestrict δ φ).toRingHom,
      x * baseChangeGL (fixSubfield φ).subtype y = baseChangeGL (fixSubfield φ).subtype y * x := by
    intro y hy
    have hjC₀ := hmap (Subgroup.mem_map_of_mem _ hy)
    have h1 := hrJ ⟨_, hC₀C hjC₀⟩ hjC₀
    have h2 := hr' ⟨_, hC₀C hjC₀⟩
    rw [h1] at h2
    change baseChangeGL (fixSubfield φ).subtype y = x * Units.map (entrywiseHom φ.toRingHom)
      (baseChangeGL (fixSubfield φ).subtype y) * x⁻¹ at h2
    rw [hφfix] at h2
    calc x * baseChangeGL (fixSubfield φ).subtype y =
        (x * baseChangeGL (fixSubfield φ).subtype y * x⁻¹) * x := by group
      _ = baseChangeGL (fixSubfield φ).subtype y * x := by rw [← h2]
  obtain ⟨-, -, hfaith, -⟩ := odd_diagram_fixed_ambient_centralizer_trivial TwistTag.E6 hp he'
    (hp.eq_two_or_odd'.resolve_left hp2).pow (fixSubfield φ) hK'card
    (fixSubfieldRestrict δ φ).toRingHom hδ' (AlgebraicClosure K)
    ((algebraMap K (AlgebraicClosure K)).comp (fixSubfield φ).subtype)
  have hzG : baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
      adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rw [hx, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag (AlgebraicClosure K) _).1
  have hz1 : baseChangeGL (algebraMap K (AlgebraicClosure K)) x = 1 := by
    refine hfaith _ hzG ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [← baseChangeGL_baseChangeGL, ← map_mul, ← map_mul, hxC y hy]
  have hx1 : x = 1 :=
    baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) (by rw [hz1, map_one])
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin TwistTag.E6.foldedTag.rank, (TwistTag.E6.orbit a₀).card = 1 :=
    ⟨⟨2, by decide⟩, by decide⟩
  have hφK₀ : ∀ c, δ c = c → φ c = c := by
    intro c hc
    have hcO : c ∈ orbitField TwistTag.E6 K δ.toRingHom a₀ :=
      mem_orbitField.2 (by rw [ha₀, pow_one]; exact hc)
    have hxC₀ : (xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a₀) c :
        ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K δ.toRingHom := by
      have h := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K δ.toRingHom
        (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 δ.toRingHom a₀ ⟨c, hcO⟩)
      rwa [coe_orbitX_of_card_eq_one ha₀] at h
    have h1 := hrJ (adjX TwistTag.E6.tag K (TwistTag.E6.orbitMin a₀) c) hxC₀
    have h2 := hr' (adjX TwistTag.E6.tag K (TwistTag.E6.orbitMin a₀) c)
    rw [h1, hx1, one_mul, inv_one, mul_one] at h2
    change xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a₀) c = Units.map
      (entrywiseHom φ.toRingHom) (xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a₀) c) at h2
    rw [units_map_entrywiseHom_xUnit] at h2
    exact adjX_injective (TwistTag.E6.orbitMin a₀) (Subtype.ext h2.symm)
  have hφ1 : φ = 1 :=
    eq_one_of_odd_of_mem_zpowers hδ2 (UnbalancedCatalog.mem_zpowers_of_fixed hφK₀) hφo
  have hid : ∀ y : ModGL TwistTag.E6.tag K,
      Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) y = y := fun y => Units.ext (entrywise_id _)
  subst hφ1
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [hr', hx1, hid]
  simp

theorem outerCoreAt_graph_field_E6
    {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup TwistTag.E6.tag K)} {g : adjointGroup TwistTag.E6.tag K}
    {a : Fin TwistTag.E6.tag.rank → Kˣ}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
            (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hα : α ^ 2 = 1) : OuterCoreAt α := by
  obtain ⟨-, β, hβ, hβα⟩ :=
    exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, hψ, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hψ' : ψ * α * ψ⁻¹ = β := MulEquiv.ext fun u => Subtype.ext ((hψ u).trans (hβ u).symm)
  exact outerCoreAt_of_conj hψ' (outerCoreTrivAt_graph_field_E6 hp hp2 he hKe δ hδ hβ).outerCoreAt

@[expose] def E6GraphCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    ∀ α : MulAut (adjointGroup TwistTag.E6.tag K), α ^ 2 = 1 →
      ∀ (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ),
        (∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
          (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
            diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹ *
              (rootDiagUnit TwistTag.E6.tag a)⁻¹ * (g : ModGL TwistTag.E6.tag K)⁻¹) →
      OuterCoreAt α

theorem outerCoreAt_E6_of_subrows
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) (hinn : InnerDiagCoreInput .E6)
    (hgr : E6GraphCoreInput) (α : MulAut (adjointGroup Tag.E6 K)) (hα : orderOf α = 2) :
    OuterCoreAt α := by
  have hα2 : α ^ 2 = 1 := sq_eq_one_of_orderOf hα
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    exact absurd hα (by norm_num)
  obtain ⟨p, f, hp, hp2, hf, -, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have h1 : ∀ x : ModGL Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF α
  have hσ2 := hsq α g a σ ε hgaσ hα2
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.isLt
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε with hε | hε
    ·
      refine hinn K hK α hα2 hα1 g a fun h => ?_
      rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]
    ·
      exact hgr K hK α hα2 g a fun h => (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)
  ·
    obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hcard σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hcard]
    rcases hε with hε | hε
    ·
      refine outerCoreAt_quadratic_field_E (Or.inl rfl) hK hp he hKe σ hσc (g := g) (a := a)
        (fun h => ?_) hα2
      rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]
    ·
      exact outerCoreAt_graph_field_E6 hp hp2 he hKe σ hσc
        (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl)) hα2

theorem oddLieCoreFamilyInput_E6
    (hinn : InnerDiagCoreInput .E6) (hgr : E6GraphCoreInput) : OddLieCoreFamilyInput .E6 := by
  refine oddLieCoreFamilyInput_of_outerCoreAt fun S _ _ _ _ n p f hp hp2 _ hm i hi => ?_
  refine outerCoreAt_of_lieModel_untwisted .E6 hm (fun G _ hG => hG.2) ⟨by decide, by decide,
    by decide⟩ (fun K _ _ hK β hβ => ?_) i hi
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  exact outerCoreAt_E6_of_subrows hodd hinn hgr β hβ

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
