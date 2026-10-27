module

public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.SingleEdgePerfect
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.LieType.Chevalley.NativeMonomial

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped commutatorElement

section Auts

variable (t : TwistTag) (K : Type) [Field K]

@[expose] def diagramConjAut :
    MulAut (adjointGroup t.tag K) :=
  twistEquiv t K (RingHom.id K) Function.surjective_id

theorem coe_diagramConjAut
    (g : adjointGroup t.tag K) :
    (diagramConjAut t K g : ModGL t.tag K) = diagramMap t K * g * (diagramMap t K)⁻¹ := by
  change twistHom t K (RingHom.id K) g = _
  rw [← conj_diagramMap_eq_twistHom]
  rfl

variable (τ : Tag) {K}

@[expose] def entrywiseAdjointAut
    (δ : K ≃+* K) : MulAut (adjointGroup τ K) :=
  mulAutRestrict (adjointGroup τ K) (exactEntrywiseAut τ δ) (map_exactEntrywiseAut δ (Or.inl rfl))

theorem coe_entrywiseAdjointAut
    (δ : K ≃+* K) (g : adjointGroup τ K) :
    (entrywiseAdjointAut τ δ g : ModGL τ K) = Units.map (entrywiseHom δ.toRingHom) g :=
  rfl

end Auts

section General

variable {G : Type*} [Group G]

@[expose] def DerivedFixedSubgroupData (C J : Subgroup G) (η : MulAut C) : Prop :=
  orderOf η = 2 ∧ J ≤ C ∧
    ⁅MonoidHom.eqLocus η.toMonoidHom (MonoidHom.id C),
      MonoidHom.eqLocus η.toMonoidHom (MonoidHom.id C)⁆ = J.subgroupOf C ∧
    Finite J ∧ IsSimpleGroup J ∧ Even (Nat.card J) ∧
    Set.InjOn (MulAut.conj : C →* MulAut C) (J.subgroupOf C) ∧
    (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer {η} ∧
    (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer {η})).Normal

theorem commutator_subgroupOf_eq {C H : Subgroup G} (hH : H ≤ C) :
    ⁅H.subgroupOf C, H.subgroupOf C⁆ = (⁅H, H⁆).subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hH,
    Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self H).trans hH)]

theorem derivedFixed_inner_normal {C J : Subgroup G} {η : MulAut C}
    (hZ : Subgroup.center C = ⊥)
    (hJ : ⁅MonoidHom.eqLocus η.toMonoidHom (MonoidHom.id C),
      MonoidHom.eqLocus η.toMonoidHom (MonoidHom.id C)⁆ = J.subgroupOf C) :
    Set.InjOn (MulAut.conj : C →* MulAut C) (J.subgroupOf C) ∧
    (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer {η} ∧
    (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer {η})).Normal := by
  set F := MonoidHom.eqLocus η.toMonoidHom (MonoidHom.id C)
  have hJF : J.subgroupOf C ≤ F := hJ ▸ Subgroup.commutator_le_self F
  refine ⟨fun g _ g' _ h => mulAut_conj_injective_of_center_eq_bot hZ h, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgfix : η g = g := hJF hg
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hgfix]
  · constructor
    intro n hn β
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨g, hg, hgn⟩ := hn
    obtain ⟨β, hβ⟩ := β
    have hβ' := Subgroup.mem_centralizer_singleton_iff.1 hβ
    have hβF : F.map β.toMonoidHom ≤ F := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : η x = x := hx
      have h1 := congrArg (fun φ : MulAut C => φ x) hβ'
      simp only [MulAut.mul_apply] at h1
      change η (β x) = β x
      rw [← h1, hx']
    refine ⟨β g, ?_, ?_⟩
    · rw [← hJ] at hg ⊢
      have hmap : (⁅F, F⁆).map β.toMonoidHom ≤ ⁅F, F⁆ := by
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono hβF hβF
      exact hmap ⟨g, hg, rfl⟩
    · change MulAut.conj (β g) = β * (n : MulAut C) * β⁻¹
      rw [← hgn, mulAut_mul_conj_mul_inv]

theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (hZ : Subgroup.center Q = ⊥) : IsSimpleGroup Q :=
  CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hQ
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

end General

section Field

variable {τ : Tag} {K : Type} [Field K]

theorem commutator_adjointGroup_eq_of_single_edge
    (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K := by
  have h := single_edge_perfect τ K hτ
  rw [commutator_def] at h
  have e := congrArg (Subgroup.map (adjointGroup τ K).subtype) h
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at e

variable [Finite K]

theorem commutator_entrywiseFixedGroup_le
    (σ : K ≃+* K) :
    ⁅entrywiseFixedGroup τ σ, entrywiseFixedGroup τ σ⁆ ≤ fixedFieldImage τ σ := by
  obtain ⟨-, -, -, hJΓ, -, hnormal, hcomm⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hq := hcomm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hq
  have hmem := Subgroup.mem_subgroupOf.1 hq
  have e : (((⟨a, ha⟩ * ⟨b, hb⟩ : entrywiseFixedGroup τ σ)⁻¹ *
      (⟨b, hb⟩ * ⟨a, ha⟩) : entrywiseFixedGroup τ σ) : ModGL τ K) = b⁻¹ * a⁻¹ * b * a := by
    simp [mul_assoc]
  rw [e] at hmem
  have hinv : (b⁻¹ * a⁻¹ * b * a)⁻¹ ∈ fixedFieldImage τ σ := inv_mem hmem
  have hconj : b * a * (b⁻¹ * a⁻¹ * b * a)⁻¹ * (b * a)⁻¹ ∈ fixedFieldImage τ σ := by
    have := hnormal.conj_mem ⟨_, hJΓ hinv⟩ (Subgroup.mem_subgroupOf.2 hinv)
      (⟨b, hb⟩ * ⟨a, ha⟩)
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  have e2 : b * a * (b⁻¹ * a⁻¹ * b * a)⁻¹ * (b * a)⁻¹ = ⁅a, b⁆ := by
    rw [commutatorElement_def]
    group
  rwa [e2] at hconj

theorem commutator_entrywiseFixedGroup_eq
    (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (σ : K ≃+* K) :
    ⁅entrywiseFixedGroup τ σ, entrywiseFixedGroup τ σ⁆ = fixedFieldImage τ σ := by
  refine le_antisymm (commutator_entrywiseFixedGroup_le σ) ?_
  have hJ : ⁅fixedFieldImage τ σ, fixedFieldImage τ σ⁆ = fixedFieldImage τ σ := by
    rw [fixedFieldImage, ← Subgroup.map_commutator, commutator_adjointGroup_eq_of_single_edge hτ]
  rw [← hJ]
  exact Subgroup.commutator_mono fixedFieldImage_le fixedFieldImage_le

end Field


theorem even_E6_canonical_field_graph_field_derived_fixed_subgroups
    {e : ℕ} (he : 1 ≤ e)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ e)) :
    DerivedFixedSubgroupData (adjointGroup TwistTag.E6.tag K) (fixedFieldImage TwistTag.E6.tag σ)
      (diagramConjAut TwistTag.E6 K ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ) ∧
    DerivedFixedSubgroupData (adjointGroup TwistTag.E6.tag K)
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      (diagramConjAut TwistTag.E6 K ^ 1 * entrywiseAdjointAut TwistTag.E6.tag σ) := by
  classical
  rw [pow_zero, one_mul, pow_one]
  set C := adjointGroup TwistTag.E6.tag K
  set δ := entrywiseAdjointAut TwistTag.E6.tag σ
  set γ := diagramConjAut TwistTag.E6 K
  have hδc : ∀ g : C, (δ g : ModGL TwistTag.E6.tag K) = Units.map (entrywiseHom σ.toRingHom) g :=
    fun _ => rfl
  have hK' : Nat.card K = (2 ^ e) ^ TwistTag.E6.order := by
    rw [hK, ← pow_mul, mul_comm]
    rfl
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos two_pos _).ne')
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨σ', hσ', hord, -, -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two he K hK'
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  rw [hσσ'] at hord
  have hord2 : orderOf σ = 2 := hord
  have hσ2 : σ ^ 2 = 1 := by
    rw [← hord2]
    exact pow_orderOf_eq_one σ
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have h := congrArg (fun φ : K ≃+* K => φ c) hσ2
    simpa only [pow_two, RingAut.mul_apply, RingAut.one_apply] using h
  have hσne : ∃ c, σ c ≠ c := by
    by_contra! h
    have h1 : σ = 1 := RingEquiv.ext h
    rw [h1, orderOf_one] at hord2
    exact absurd hord2 (by decide)
  have hZ : Subgroup.center C = ⊥ := center_adjointGroup_eq_bot_field _ K
  have hσσring : σ.toRingHom.comp σ.toRingHom = RingHom.id K := RingHom.ext hσσ
  have hδ2 : δ ^ 2 = 1 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hδc, hδc, units_map_entrywiseHom_comp,
      hσσring]
    exact Units.ext (entrywise_id _)
  have hδ1 : δ ≠ 1 := by
    obtain ⟨c, hc⟩ := hσne
    intro h
    have h1 := congrArg (fun φ : MulAut C =>
      ((φ (xElement ⟨0, by decide⟩ c) : C) : ModGL TwistTag.E6.tag K)) h
    simp only [hδc, MulAut.one_apply] at h1
    change Units.map (entrywiseHom σ.toRingHom) (xUnit TwistTag.E6.tag K ⟨0, by decide⟩ c) =
      xUnit TwistTag.E6.tag K ⟨0, by decide⟩ c at h1
    rw [units_map_entrywiseHom_xUnit] at h1
    exact hc (xOp_injective _ (congrArg Units.val h1))
  have hδord : orderOf δ = 2 := orderOf_eq_prime hδ2 hδ1
  have hγδ : ∀ g : C, ((γ * δ) g : ModGL TwistTag.E6.tag K) =
      twistHom TwistTag.E6 K σ.toRingHom g := fun g => by
    rw [MulAut.mul_apply, coe_diagramConjAut, hδc, twistHom_apply]
  have hγδ2 : (γ * δ) ^ 2 = 1 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hγδ, hγδ]
    have h := twistHom_iterate_order_of_pow_eq_one (t := TwistTag.E6) σ.toRingHom
      (RingHom.ext fun c => by
        change σ (σ c) = c
        exact hσσ c) (g : ModGL TwistTag.E6.tag K)
    exact h
  have hγδ1 : γ * δ ≠ 1 := by
    intro h
    set γ₀ : Fin TwistTag.E6.tag.rank → K := fun j => if (j : ℕ) = 0 then 1 else 0
    have hx : orbitXProd TwistTag.E6 ⟨0, by decide⟩ γ₀ ∈ C :=
      Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
        exact xUnit_mem_adjointGroup j _
    have h1 := congrArg (fun φ : MulAut C => ((φ ⟨_, hx⟩ : C) : ModGL TwistTag.E6.tag K)) h
    simp only [hγδ, MulAut.one_apply] at h1
    rw [twistHom_orbitXProd] at h1
    have key := eq_of_orbitXProd_eq TwistTag.E6 h1 ⟨0, by decide⟩ (by decide)
    have hp : TwistTag.E6.perm.symm ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide
    simp [hp, γ₀] at key
  have hγδord : orderOf (γ * δ) = 2 := orderOf_eq_prime hγδ2 hγδ1
  have hFδ : MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id C) =
      (entrywiseFixedGroup TwistTag.E6.tag σ).subgroupOf C := by
    ext g
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  have hFγδ : MonoidHom.eqLocus (γ * δ).toMonoidHom (MonoidHom.id C) =
      (twistedFixedGroup TwistTag.E6 K σ.toRingHom).subgroupOf C := by
    rw [twistedFixedGroup_subgroupOf]
    congr 1
    exact MonoidHom.ext fun g => Subtype.ext (hγδ g)
  have hΓC : twistedFixedGroup TwistTag.E6 K σ.toRingHom ≤ C :=
    twistedFixedGroup_le_adjointGroup _ _ _
  have hC0 : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ C :=
    (graphFixedRootGroup_le _ _ _).trans hΓC
  have hJ0 : fixedFieldImage TwistTag.E6.tag σ ≤ C := fixedFieldImage_le.trans inf_le_left
  have hder0 : ⁅MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id C),
      MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id C)⁆ =
        (fixedFieldImage TwistTag.E6.tag σ).subgroupOf C := by
    rw [hFδ, commutator_subgroupOf_eq (H := entrywiseFixedGroup TwistTag.E6.tag σ) inf_le_left,
      commutator_entrywiseFixedGroup_eq (τ := TwistTag.E6.tag) (Or.inr (Or.inr (Or.inl rfl)))]
  obtain ⟨-, -, hΓder, -, -⟩ :=
    finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two he K hK' σ.toRingHom hσ
  have hder1 : ⁅MonoidHom.eqLocus (γ * δ).toMonoidHom (MonoidHom.id C),
      MonoidHom.eqLocus (γ * δ).toMonoidHom (MonoidHom.id C)⁆ =
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf C := by
    rw [hFγδ, commutator_subgroupOf_eq hΓC, hΓder]
  set k := fixSubfield σ
  have hinj := baseChangeGL_injective (τ := TwistTag.E6.tag) k.subtype
  have hsimple0 : IsSimpleGroup (fixedFieldImage TwistTag.E6.tag σ) := by
    have hq := CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k
    have hZk : Subgroup.center (adjointGroup Tag.E6 k) = ⊥ := center_adjointGroup_eq_bot_field _ k
    exact CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
      ((Subgroup.equivMapOfInjective (adjointGroup Tag.E6 k) _ hinj).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm)
  have heven0 : Even (Nat.card (fixedFieldImage TwistTag.E6.tag σ)) := by
    set i₀ : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩
    set x : fixedFieldImage TwistTag.E6.tag σ :=
      ⟨xUnit TwistTag.E6.tag K i₀ 1, xUnit_mem_fixedFieldImage _ (map_one σ)⟩
    have hx2 : x ^ 2 = 1 := Subtype.ext (by
      rw [pow_two, Subgroup.coe_mul]
      change xUnit TwistTag.E6.tag K i₀ 1 * xUnit TwistTag.E6.tag K i₀ 1 = 1
      rw [← xUnit_add, one_add_one_eq_two, h2, xUnit_zero])
    have hx1 : x ≠ 1 := fun h => by
      have h' : xOp TwistTag.E6.tag K i₀ 1 = xOp TwistTag.E6.tag K i₀ 0 := by
        rw [xOp_zero]
        exact congrArg (fun g : fixedFieldImage TwistTag.E6.tag σ =>
          ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) h
      exact one_ne_zero (xOp_injective _ h')
    rw [even_iff_two_dvd, ← orderOf_eq_prime hx2 hx1]
    exact orderOf_dvd_natCard _
  have hsimple1 : IsSimpleGroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
    have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := hσσ
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq := CFSG.LieType.Simplicity.isQuasisimple_derived_twistedFixedGroup σ.toRingHom hθ h4
    have hZ1 := exceptional_fixed_center_trivial TwistTag.E6 K σ
    change Subgroup.center (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ at hZ1
    rw [← hΓder] at hZ1 ⊢
    exact isSimpleGroup_of_isQuasisimple_of_center_eq_bot hq hZ1
  have heven1 : Even (Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
    set a : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩
    set x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
      ⟨orbitX TwistTag.E6 K σ.toRingHom a 1, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ a 1)⟩
    have h2a : (1 : orbitField TwistTag.E6 K σ.toRingHom a) + 1 = 0 :=
      Subtype.ext (by
        change (1 : K) + 1 = 0
        rw [one_add_one_eq_two, h2])
    have hx2 : x ^ 2 = 1 := Subtype.ext (by
      rw [pow_two, Subgroup.coe_mul]
      change ((orbitX TwistTag.E6 K σ.toRingHom a 1 : ModGL TwistTag.E6.tag K)) *
        (orbitX TwistTag.E6 K σ.toRingHom a 1 : ModGL TwistTag.E6.tag K) = 1
      rw [← Subgroup.coe_mul, ← orbitX_add, h2a, orbitX_zero]
      rfl)
    have hx1 : x ≠ 1 := fun h => by
      have h' : orbitX TwistTag.E6 K σ.toRingHom a 1 = orbitX TwistTag.E6 K σ.toRingHom a 0 := by
        rw [orbitX_zero]
        exact Subtype.ext (congrArg (fun g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom =>
          (g : ModGL TwistTag.E6.tag K)) h)
      exact one_ne_zero (orbitX_injective σ.toRingHom a h')
    rw [even_iff_two_dvd, ← orderOf_eq_prime hx2 hx1]
    exact orderOf_dvd_natCard _
  obtain ⟨hinj0, hle0, hnormal0⟩ := derivedFixed_inner_normal hZ hder0
  obtain ⟨hinj1, hle1, hnormal1⟩ := derivedFixed_inner_normal hZ hder1
  exact ⟨⟨hδord, hJ0, hder0, inferInstance, hsimple0, heven0, hinj0, hle0, hnormal0⟩,
    ⟨hγδord, hC0, hder1, inferInstance, hsimple1, heven1, hinj1, hle1, hnormal1⟩⟩

end CFSG.LieType.Chevalley
