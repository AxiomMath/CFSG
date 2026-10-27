module

public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem commute_ringEquiv_of_finite {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) :
    Commute σ δ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  obtain ⟨φ, -, -, htop, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) hp n.pos (by rw [Nat.card_eq_fintype_card, hn])
  have hσ : σ ∈ Subgroup.zpowers φ := by
    rw [htop]
    exact Subgroup.mem_top σ
  have hδ : δ ∈ Subgroup.zpowers φ := by
    rw [htop]
    exact Subgroup.mem_top δ
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hδ
  exact Commute.zpow_zpow_self φ a b

theorem apply_apply_comm_of_finite {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) (c : K) :
    σ (δ c) = δ (σ c) :=
  congrArg (fun φ : K ≃+* K => φ c) (commute_ringEquiv_of_finite σ δ).eq

theorem map_mem_fixSubfield {K : Type} [Field K] {σ δ : K ≃+* K}
    (h : ∀ c, σ (δ c) = δ (σ c)) {c : K} (hc : c ∈ fixSubfield δ) : σ c ∈ fixSubfield δ := by
  rw [mem_fixSubfield] at hc ⊢
  rw [← h, hc]

@[expose] def fixSubfieldRestrict {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) :
    fixSubfield δ ≃+* fixSubfield δ :=
  RingEquiv.ofBijective
    (σ.toRingHom.restrict (fixSubfield δ) (fixSubfield δ) fun _ hc =>
      map_mem_fixSubfield (apply_apply_comm_of_finite σ δ) hc)
    (Finite.injective_iff_bijective.1 (RingHom.injective _))

@[simp] theorem coe_fixSubfieldRestrict {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K)
    (c : fixSubfield δ) : (fixSubfieldRestrict σ δ c : K) = σ c :=
  rfl

theorem coe_fixSubfieldRestrict_pow {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) (n : ℕ)
    (c : fixSubfield δ) : ((fixSubfieldRestrict σ δ ^ n) c : K) = (σ ^ n) (c : K) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, coe_fixSubfieldRestrict, ih, pow_succ', RingAut.mul_apply]

theorem fixSubfieldRestrict_pow_eq_one {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (δ : K ≃+* K) {n : ℕ} (hσ : σ ^ n = 1) : fixSubfieldRestrict σ δ ^ n = 1 :=
  RingEquiv.ext fun c => Subtype.ext (by rw [coe_fixSubfieldRestrict_pow, hσ]; rfl)

section Twist

variable {t : TwistTag} {K : Type} [Field K]

theorem entrywise_twistHom_comm {σ δ : K →+* K} (h : ∀ c, σ (δ c) = δ (σ c))
    (g : ModGL t.tag K) :
    Units.map (entrywiseHom δ) (twistHom t K σ g) =
      twistHom t K σ (Units.map (entrywiseHom δ) g) := by
  have e : δ.comp σ = σ.comp δ := RingHom.ext fun c => (h c).symm
  rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp,
    units_map_entrywiseHom_comp, e]

theorem entrywise_mem_twistedFixedGroup
    {σ δ : K ≃+* K} (h : ∀ c, σ (δ c) = δ (σ c))
    {g : ModGL t.tag K} (hg : g ∈ twistedFixedGroup t K σ.toRingHom) :
    Units.map (entrywiseHom δ.toRingHom) g ∈ twistedFixedGroup t K σ.toRingHom := by
  refine ⟨?_, ?_⟩
  · rw [← ((chevalley_root_character_and_field_conjugation t.tag K).2.2.2.2.1 δ).1]
    exact Subgroup.mem_map_of_mem _ hg.1
  · have hF : twistHom t K σ.toRingHom g = g := hg.2
    change twistHom t K σ.toRingHom (Units.map (entrywiseHom δ.toRingHom) g) =
      Units.map (entrywiseHom δ.toRingHom) g
    rw [← entrywise_twistHom_comm (σ := σ.toRingHom) (δ := δ.toRingHom) h, hF]

theorem map_entrywise_twistedFixedGroup
    {σ δ : K ≃+* K} (h : ∀ c, σ (δ c) = δ (σ c)) :
    (twistedFixedGroup t K σ.toRingHom).map (Units.map (entrywiseHom δ.toRingHom)) =
      twistedFixedGroup t K σ.toRingHom := by
  have h' : ∀ c, σ (δ.symm c) = δ.symm (σ c) := fun c => by
    apply δ.injective
    rw [← h, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact entrywise_mem_twistedFixedGroup h hg
  · exact ⟨_, entrywise_mem_twistedFixedGroup h' hg, exactEntrywiseAut_right_inv δ g⟩

theorem map_entrywise_commutator_twistedFixedGroup
    {σ δ : K ≃+* K}
    (h : ∀ c, σ (δ c) = δ (σ c)) :
    ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆.map
        (Units.map (entrywiseHom δ.toRingHom)) =
      ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ := by
  rw [Subgroup.map_commutator, map_entrywise_twistedFixedGroup h]

end Twist

theorem twistHom_baseChangeGL
    {t : TwistTag} {k K : Type} [Field k] [Field K] (ι : k →+* K)
    {σk : k →+* k} {σ : K →+* K} (h : ι.comp σk = σ.comp ι) (g : ModGL t.tag k) :
    twistHom t K σ (baseChangeGL ι g) = baseChangeGL ι (twistHom t k σk g) := by
  have e : Units.map (entrywiseHom σ) (baseChangeGL ι g) =
      baseChangeGL ι (Units.map (entrywiseHom σk) g) := by
    change baseChangeGL σ (baseChangeGL ι g) = baseChangeGL ι (baseChangeGL σk g)
    rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h]
  rw [twistHom_apply, twistHom_apply, e, map_mul, map_mul, map_inv, baseChangeGL_diagramMap]

section Image

variable {t : TwistTag} {K : Type} [Field K] [Finite K] {σ δ : K ≃+* K}

omit [Finite K] in
theorem map_baseChangeGL_twistedFixedGroup_eq
    {σk : fixSubfield δ →+* fixSubfield δ}
    (hσk : ∀ c : fixSubfield δ, (σk c : K) = σ c) :
    (twistedFixedGroup t (fixSubfield δ) σk).map (baseChangeGL (fixSubfield δ).subtype) =
      fixedFieldImage t.tag δ ⊓
        (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ) := by
  have hισ : (fixSubfield δ).subtype.comp σk = σ.toRingHom.comp (fixSubfield δ).subtype :=
    RingHom.ext fun c => hσk c
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    have hgJ : baseChangeGL (fixSubfield δ).subtype g ∈ fixedFieldImage t.tag δ :=
      ⟨g, hg.1, rfl⟩
    refine ⟨hgJ, ⟨baseChangeGL_mem_adjointGroup _ hg.1, ?_⟩, fixedFieldImage_le hgJ⟩
    have hF : twistHom t (fixSubfield δ) σk g = g := hg.2
    change twistHom t K σ.toRingHom (baseChangeGL (fixSubfield δ).subtype g) =
      baseChangeGL (fixSubfield δ).subtype g
    rw [twistHom_baseChangeGL _ hισ, hF]
  · rintro _ ⟨⟨g, hg, rfl⟩, hgΓ, -⟩
    refine ⟨g, ⟨hg, baseChangeGL_injective (fixSubfield δ).subtype ?_⟩, rfl⟩
    have hF : twistHom t K σ.toRingHom (baseChangeGL (fixSubfield δ).subtype g) =
        baseChangeGL (fixSubfield δ).subtype g := hgΓ.2
    rw [← twistHom_baseChangeGL _ hισ]
    exact hF

variable (t σ δ)

theorem map_baseChangeGL_twistedFixedGroup_le :
    (twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
        (baseChangeGL (fixSubfield δ).subtype) ≤
      twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ := by
  rw [map_baseChangeGL_twistedFixedGroup_eq (coe_fixSubfieldRestrict σ δ)]
  exact inf_le_right

theorem map_baseChangeGL_twistedFixedGroup_normal :
    (((twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
        (baseChangeGL (fixSubfield δ).subtype)).subgroupOf
      (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff
    (map_baseChangeGL_twistedFixedGroup_le t σ δ)).2 fun l y hl hy => ?_
  rw [map_baseChangeGL_twistedFixedGroup_eq (coe_fixSubfieldRestrict σ δ),
    Subgroup.mem_inf] at hl ⊢
  refine ⟨?_, mul_mem (mul_mem hy hl.2) (inv_mem hy)⟩
  have hmem := (fixedFieldImage_normal (τ := t.tag) (σ := δ)).conj_mem
    ⟨l, (Subgroup.mem_inf.1 hl.2).2⟩ (Subgroup.mem_subgroupOf.2 hl.1)
    ⟨y, (Subgroup.mem_inf.1 hy).2⟩
  exact Subgroup.mem_subgroupOf.1 hmem

instance map_baseChangeGL_twistedFixedGroup_subgroupOf_normal :
    (((twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
        (baseChangeGL (fixSubfield δ).subtype)).subgroupOf
      (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ)).Normal :=
  map_baseChangeGL_twistedFixedGroup_normal t σ δ

theorem map_baseChangeGL_twistedFixedGroup_quotient_comm
    (a b : ↥(twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ) ⧸
      ((twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
        (baseChangeGL (fixSubfield δ).subtype)).subgroupOf
      (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ)) :
    a * b = b * a := by
  induction a using QuotientGroup.induction_on with | H y₁ => ?_
  induction b using QuotientGroup.induction_on with | H y₂ => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, map_baseChangeGL_twistedFixedGroup_eq (coe_fixSubfieldRestrict σ δ)]
  refine ⟨?_, ((y₁ * y₂)⁻¹ * (y₂ * y₁)).2⟩
  have hx := entrywiseFixedGroup_quotient_comm (τ := t.tag) (σ := δ)
    (QuotientGroup.mk ⟨y₁, (Subgroup.mem_inf.1 y₁.2).2⟩)
    (QuotientGroup.mk ⟨y₂, (Subgroup.mem_inf.1 y₂.2).2⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hx
  exact hx

end Image


theorem diagram_coordinate_common_fixed_structure
    (t : TwistTag) (K : Type) [Field K]
    [Finite K] (σ δ : K ≃+* K) (hσ : σ ^ t.order = 1) :
    (∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ c : K) = σ c) ∧
    fixSubfieldRestrict σ δ ^ t.order = 1 ∧
    (∀ g : ModGL t.tag K, Units.map (entrywiseHom δ.toRingHom) (twistHom t K σ.toRingHom g) =
      twistHom t K σ.toRingHom (Units.map (entrywiseHom δ.toRingHom) g)) ∧
    (twistedFixedGroup t K σ.toRingHom).map (Units.map (entrywiseHom δ.toRingHom)) =
      twistedFixedGroup t K σ.toRingHom ∧
    ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆.map
        (Units.map (entrywiseHom δ.toRingHom)) =
      ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ ∧
    fixedFieldImage t.tag δ ≤ entrywiseFixedGroup t.tag δ ∧
    ((fixedFieldImage t.tag δ).subgroupOf (entrywiseFixedGroup t.tag δ)).Normal ∧
    (∀ a b : ↥(entrywiseFixedGroup t.tag δ) ⧸
        (fixedFieldImage t.tag δ).subgroupOf (entrywiseFixedGroup t.tag δ), a * b = b * a) ∧
    (twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
        (baseChangeGL (fixSubfield δ).subtype) =
      fixedFieldImage t.tag δ ⊓
        (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ) ∧
    (((twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
        (baseChangeGL (fixSubfield δ).subtype)).subgroupOf
      (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ)).Normal ∧
    (∀ a b : ↥(twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ) ⧸
        ((twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
          (baseChangeGL (fixSubfield δ).subtype)).subgroupOf
        (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ), a * b = b * a) ∧
    ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ ⊓
        entrywiseFixedGroup t.tag δ ≤
      twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ ∧
    ((⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ ⊓
        entrywiseFixedGroup t.tag δ).subgroupOf
      (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ)).Normal ∧
    ∃ e : ↥(twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom) ≃*
        ↥((twistedFixedGroup t (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
          (baseChangeGL (fixSubfield δ).subtype)),
      ∀ g, (e g : ModGL t.tag K) = baseChangeGL (fixSubfield δ).subtype g := by
  have hcomm := apply_apply_comm_of_finite σ δ
  obtain ⟨-, -, -, hJX, -, hJn, hXJ⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup t.tag K δ
  have hDY : ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ ⊓
        entrywiseFixedGroup t.tag δ ≤
      twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ := fun g hg =>
    ⟨Subgroup.commutator_le_self _ hg.1, hg.2⟩
  have hDn : ((⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ ⊓
        entrywiseFixedGroup t.tag δ).subgroupOf
      (twistedFixedGroup t K σ.toRingHom ⊓ entrywiseFixedGroup t.tag δ)).Normal :=
    (Subgroup.normal_subgroupOf_iff hDY).2 fun d y hd hy => by
      rw [Subgroup.mem_inf] at hd hy ⊢
      exact ⟨conj_mem_commutator_self hy.1 hd.1, mul_mem (mul_mem hy.2 hd.2) (inv_mem hy.2)⟩
  exact ⟨coe_fixSubfieldRestrict σ δ, fixSubfieldRestrict_pow_eq_one δ hσ,
    entrywise_twistHom_comm (σ := σ.toRingHom) (δ := δ.toRingHom) hcomm,
    map_entrywise_twistedFixedGroup hcomm, map_entrywise_commutator_twistedFixedGroup hcomm,
    hJX, hJn, hXJ, map_baseChangeGL_twistedFixedGroup_eq (coe_fixSubfieldRestrict σ δ),
    map_baseChangeGL_twistedFixedGroup_normal t σ δ,
    map_baseChangeGL_twistedFixedGroup_quotient_comm t σ δ, hDY, hDn,
    Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _),
    fun g => Subgroup.coe_equivMapOfInjective_apply _ _ _ g⟩

end CFSG.LieType.Chevalley
