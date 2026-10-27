module

public import CFSG.LieType.Chevalley.GraphFixedF4Group
public import CFSG.LieType.Chevalley.GraphFixedCommonBaseField
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Simplicity.Exceptional

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section General

variable {G : Type*} [Group G]

@[expose] def conjRestrict (C : Subgroup G) (P : G)
    (hP : C.map (MulAut.conj P).toMonoidHom = C) : MulAut C :=
  ((MulAut.conj P).subgroupMap C).trans (MulEquiv.subgroupCongr hP)

theorem coe_conjRestrict (C : Subgroup G) (P : G) (hP : C.map (MulAut.conj P).toMonoidHom = C)
    (g : C) : (conjRestrict C P hP g : G) = P * g * P⁻¹ :=
  rfl

@[expose] def CanonicalGraphFixedSubgroup (C J : Subgroup G) (P : G) : Prop :=
  ∃ η : MulAut C, (∀ g : C, (η g : G) = P * g * P⁻¹) ∧ orderOf η = 2 ∧ J ≤ C ∧
    (∀ g : C, η g = g ↔ (g : G) ∈ J) ∧ IsSimpleGroup J ∧ Even (Nat.card J) ∧
    Set.InjOn (MulAut.conj : C →* MulAut C) (J.subgroupOf C) ∧
    (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer {η} ∧
    (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer {η})).Normal

theorem mulAut_conj_injective_of_center_eq_bot {H : Type*} [Group H]
    (hZ : Subgroup.center H = ⊥) : Function.Injective (MulAut.conj : H →* MulAut H) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut H => φ x) h
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem mulAut_mul_conj_mul_inv {H : Type*} [Group H] (φ : MulAut H) (g : H) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem canonicalGraphFixedSubgroup_of {C J : Subgroup G} {P : G}
    (hP : C.map (MulAut.conj P).toMonoidHom = C) (hP2 : P * P = 1)
    (hne : ∃ x ∈ C, P * x * P⁻¹ ≠ x) (hJC : J ≤ C)
    (hfix : ∀ g ∈ C, P * g * P⁻¹ = g ↔ g ∈ J) (hsimple : IsSimpleGroup J)
    (heven : Even (Nat.card J)) (hZ : Subgroup.center C = ⊥) :
    CanonicalGraphFixedSubgroup C J P := by
  set η := conjRestrict C P hP
  have hη : ∀ g : C, η g = g ↔ (g : G) ∈ J := fun g =>
    ⟨fun h => (hfix g g.2).1 (congrArg Subtype.val h),
      fun h => Subtype.ext ((hfix g g.2).2 h)⟩
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hP2).symm
  refine ⟨η, fun g => rfl, ?_, hJC, hη, hsimple, heven, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ fun h => ?_
    · ext g
      change P * (P * (g : G) * P⁻¹) * P⁻¹ = g
      rw [hPinv, ← mul_assoc, ← mul_assoc, hP2, one_mul, mul_assoc, hP2, mul_one]
    · obtain ⟨x, hx, hx'⟩ := hne
      exact hx' (congrArg Subtype.val (MulEquiv.ext_iff.1 h ⟨x, hx⟩))
  · exact fun g _ g' _ h => mulAut_conj_injective_of_center_eq_bot hZ h
  · rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgfix : η g = g := (hη g).2 hg
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hgfix]
  · constructor
    intro n hn c
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨g, hg, hgn⟩ := hn
    obtain ⟨α, hα⟩ := c
    have hα' := Subgroup.mem_centralizer_singleton_iff.1 hα
    refine ⟨α g, ?_, ?_⟩
    · show α g ∈ J.subgroupOf C
      rw [Subgroup.mem_subgroupOf, ← hη]
      have hgfix : η g = g := (hη g).2 hg
      have := congrArg (fun φ : MulAut C => φ g) hα'
      simp only [MulAut.mul_apply] at this
      rw [← this, hgfix]
    · change MulAut.conj (α g) = α * (n : MulAut C) * α⁻¹
      rw [← hgn, mulAut_mul_conj_mul_inv]

end General

section F4

variable {k : Type} [Field k] [Finite k]

variable (k) in
@[expose] def adjointQuotientF4Equiv :
    AdjointQuotient .F4 k ≃* adjointGroup Tag.F4 k :=
  (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot

theorem isSimpleGroup_of_mulEquiv_adjointGroup_F4
    {H : Type} [Group H] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (e : H ≃* adjointGroup Tag.F4 k) : IsSimpleGroup H :=
  (CFSG.LieType.Simplicity.fam_f4_simplicity H 2 f
    ⟨⟨Nat.prime_two, hf, rfl⟩, k, inferInstance, inferInstance, hk,
      ⟨e.trans (adjointQuotientF4Equiv k).symm⟩⟩).2

omit [Finite k] in
theorem orderOf_xElement_F4
    (h2 : (2 : k) = 0) :
    orderOf (xElement (τ := Tag.F4) ⟨0, by decide⟩ (1 : k)) = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · refine Subtype.ext ?_
    rw [pow_two, Subgroup.coe_mul]
    change xUnit Tag.F4 k ⟨0, by decide⟩ 1 * xUnit Tag.F4 k ⟨0, by decide⟩ 1 = 1
    rw [← xUnit_add, one_add_one_eq_two, h2, xUnit_zero]
  · have h' : xOp Tag.F4 k ⟨0, by decide⟩ 1 = xOp Tag.F4 k ⟨0, by decide⟩ 0 := by
      rw [xOp_zero]
      exact congrArg (fun g : adjointGroup Tag.F4 k =>
        ((g : ModGL Tag.F4 k) : Module.End k (RootModule Tag.F4 k))) h
    exact one_ne_zero (xOp_injective _ h')

omit [Finite k] in
theorem even_card_of_mulEquiv_adjointGroup_F4
    {H : Type} [Group H] (h2 : (2 : k) = 0)
    (e : H ≃* adjointGroup Tag.F4 k) : Even (Nat.card H) := by
  rw [Nat.card_congr e.toEquiv, even_iff_two_dvd, ← orderOf_xElement_F4 h2]
  exact orderOf_dvd_natCard _

end F4

section Image

variable {k : Type} [Field k] {K : Type} [Field K]

@[expose] def graphFixedImageF4Equiv
    (ι : k →+* K) (h2 : (2 : k) = 0) :
    (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι) ≃*
      adjointGroup Tag.F4 k :=
  (Subgroup.equivMapOfInjective _ (baseChangeGL ι) (baseChangeGL_injective ι)).symm.trans
    (e6FixedF4Equiv k h2)

theorem graphFixedImageF4Equiv_apply
    (ι : k →+* K) (h2 : (2 : k) = 0)
    (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k))
    (x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι))
    (hx : (x : ModGL TwistTag.E6.tag K) = baseChangeGL ι g) :
    (graphFixedImageF4Equiv ι h2 x : ModGL Tag.F4 k) = e6FixedToF4 k g := by
  have hgx : (Subgroup.equivMapOfInjective _ (baseChangeGL ι) (baseChangeGL_injective ι)) g = x :=
    Subtype.ext (by rw [Subgroup.coe_equivMapOfInjective_apply, hx])
  rw [graphFixedImageF4Equiv, MulEquiv.trans_apply, ← hgx, MulEquiv.symm_apply_apply]
  rfl

end Image

section Conj

variable {K : Type} [Field K]

theorem diagramMap_E6_mul_self :
    diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K = 1 := by
  have h := diagramMap_pow_order TwistTag.E6 K
  rwa [show TwistTag.E6.order = 2 from rfl, pow_two] at h

theorem diagramMap_conj_orbitXProd_ne
    {γ : Fin TwistTag.E6.tag.rank → K}
    (hγ : γ ⟨5, by decide⟩ ≠ γ ⟨0, by decide⟩) :
    diagramMap TwistTag.E6 K * orbitXProd TwistTag.E6 ⟨0, by decide⟩ γ *
      (diagramMap TwistTag.E6 K)⁻¹ ≠ orbitXProd TwistTag.E6 ⟨0, by decide⟩ γ := by
  intro h
  have h' : twistHom TwistTag.E6 K (RingHom.id K) (orbitXProd TwistTag.E6 ⟨0, by decide⟩ γ) =
      orbitXProd TwistTag.E6 ⟨0, by decide⟩ γ := by
    rw [← conj_diagramMap_eq_twistHom TwistTag.E6 K]
    exact h
  rw [twistHom_orbitXProd] at h'
  have key := eq_of_orbitXProd_eq TwistTag.E6 h' ⟨0, by decide⟩ (by decide)
  have hp : TwistTag.E6.perm.symm ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide
  rw [hp, RingHom.id_apply] at key
  exact hγ key

end Conj

section Ordinary

variable (k : Type) [Field k]

theorem baseChangeGL_id
    {τ : Tag} (g : ModGL τ k) : baseChangeGL (RingHom.id k) g = g :=
  Units.ext ((baseChange_baseChangeEnd (RingHom.id k) _).unique fun b => by simp)

theorem map_baseChangeGL_id
    {τ : Tag} (H : Subgroup (ModGL τ k)) :
    H.map (baseChangeGL (RingHom.id k)) = H := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    rwa [baseChangeGL_id]
  · intro hg
    exact ⟨g, hg, baseChangeGL_id k g⟩

variable [Finite k]

theorem canonicalGraphFixedSubgroup_adjointGroup
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (h2 : (2 : k) = 0) :
    CanonicalGraphFixedSubgroup (adjointGroup TwistTag.E6.tag k)
      ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k)))
      (diagramMap TwistTag.E6 k) := by
  have hJ := map_baseChangeGL_id k (twistedFixedGroup TwistTag.E6 k (RingHom.id k))
  have e := graphFixedImageF4Equiv (RingHom.id k) h2
  refine canonicalGraphFixedSubgroup_of ?_ diagramMap_E6_mul_self ?_ ?_ ?_
    (isSimpleGroup_of_mulEquiv_adjointGroup_F4 hf hk e) (even_card_of_mulEquiv_adjointGroup_F4 h2 e)
    center_adjointGroup_eq_bot
  · rw [conj_diagramMap_eq_twistHom TwistTag.E6 k]
    exact map_twistHom_adjointGroup _ _ _ fun x => ⟨x, rfl⟩
  · set γ : Fin TwistTag.E6.tag.rank → k := fun j => if (j : ℕ) = 0 then 1 else 0
    refine ⟨orbitXProd TwistTag.E6 ⟨0, by decide⟩ γ, Subgroup.list_prod_mem _ fun x hx => ?_,
      diagramMap_conj_orbitXProd_ne (by simp [γ])⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact xUnit_mem_adjointGroup j _
  · rw [hJ]
    exact inf_le_left
  · intro g hg
    rw [hJ, mem_twistedFixedGroup_id_iff, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨hg, h⟩, fun h => h.2⟩

end Ordinary

section Twisted

variable {k K : Type} [Field k] [Field K] [Algebra k K] {σ : K →+* K}

theorem f4OrbitXUnit_eq_orbitX_of_fixed
    (j : Fin Tag.F4.rank) {d : K} (hd : σ d = d) :
    f4OrbitXUnit K j d = (orbitX TwistTag.E6 K σ (f4FoldedIndex j)
      ⟨d, mem_orbitField_of_fixed hd _⟩ : ModGL TwistTag.E6.tag K) := by
  rw [coe_orbitX, f4OrbitXUnit, TwistTag.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun n _ => ?_)
  rw [Function.comp_apply, ringHom_pow_apply_eq_of_apply_eq hd]

theorem f4OrbitYUnit_eq_orbitY_of_fixed
    (j : Fin Tag.F4.rank) {d : K} (hd : σ d = d) :
    f4OrbitYUnit K j d = (orbitY TwistTag.E6 K σ (f4FoldedIndex j)
      ⟨d, mem_orbitField_of_fixed hd _⟩ : ModGL TwistTag.E6.tag K) := by
  rw [coe_orbitY, f4OrbitYUnit, TwistTag.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun n _ => ?_)
  rw [Function.comp_apply, ringHom_pow_apply_eq_of_apply_eq hd]

omit [Algebra k K] in
theorem baseChangeGL_f4OrbitXUnit
    (ι : k →+* K) (j : Fin Tag.F4.rank) (c : k) :
    baseChangeGL ι (f4OrbitXUnit k j c) = f4OrbitXUnit K j (ι c) := by
  rw [f4OrbitXUnit, f4OrbitXUnit, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => baseChangeGL_xUnit ι i c)

omit [Algebra k K] in
theorem baseChangeGL_f4OrbitYUnit
    (ι : k →+* K) (j : Fin Tag.F4.rank) (c : k) :
    baseChangeGL ι (f4OrbitYUnit k j c) = f4OrbitYUnit K j (ι c) := by
  rw [f4OrbitYUnit, f4OrbitYUnit, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => baseChangeGL_yUnit ι i c)

theorem map_baseChangeGL_le_graphFixedRootGroup
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c) :
    (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) ≤
      graphFixedRootGroup TwistTag.E6 K σ := by
  rw [twistedFixedGroup_id_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨j, c, rfl | rfl⟩, rfl⟩
  · rw [baseChangeGL_f4OrbitXUnit, f4OrbitXUnit_eq_orbitX_of_fixed j (hfix c)]
    exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
  · rw [baseChangeGL_f4OrbitYUnit, f4OrbitYUnit_eq_orbitY_of_fixed j (hfix c)]
    exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
      (orbitY_mem_graphFixedNegUnipotent _ _ _ _)

theorem diagramMap_conj_eq_entrywise (hσσ : ∀ c, σ (σ c) = c) {h : ModGL TwistTag.E6.tag K}
    (hΓ : h ∈ twistedFixedGroup TwistTag.E6 K σ) :
    diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹ =
      Units.map (entrywiseHom σ) h := by
  have h1 := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).1 hΓ).2
  rw [twistHom_apply] at h1
  have h2 := congrArg (Units.map (entrywiseHom σ)) h1
  rw [map_mul, map_mul, map_inv, units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp,
    show σ.comp σ = RingHom.id K from RingHom.ext hσσ,
    show Units.map (entrywiseHom (RingHom.id K)) h = h from Units.ext (entrywise_id _)] at h2
  exact h2

theorem map_conj_diagramMap_graphFixedRootGroup
    (σE : K ≃+* K) (hσE : σE.toRingHom = σ)
    (hσσ : ∀ c, σ (σ c) = c) :
    (graphFixedRootGroup TwistTag.E6 K σ).map (MulAut.conj (diagramMap TwistTag.E6 K)).toMonoidHom =
      graphFixedRootGroup TwistTag.E6 K σ := by
  have hmem : ∀ h ∈ graphFixedRootGroup TwistTag.E6 K σ,
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹ ∈
        graphFixedRootGroup TwistTag.E6 K σ := fun h hh => by
    rw [diagramMap_conj_eq_entrywise hσσ (graphFixedRootGroup_le _ _ _ hh)]
    have e : ∀ x, σE x = σ x := fun x => by rw [← hσE]; rfl
    have := units_map_entrywiseHom_mem_graphFixedRootGroup (δ := σE) (fun c => by rw [e, e]) hh
    rwa [hσE] at this
  have hP2 := diagramMap_E6_mul_self (K := K)
  have hPinv : (diagramMap TwistTag.E6 K)⁻¹ = diagramMap TwistTag.E6 K :=
    (eq_inv_of_mul_eq_one_left hP2).symm
  refine le_antisymm ?_ fun h hh => ?_
  · rintro _ ⟨h, hh, rfl⟩
    exact hmem h hh
  · refine ⟨_, hmem h hh, ?_⟩
    change diagramMap TwistTag.E6 K * (diagramMap TwistTag.E6 K * h *
      (diagramMap TwistTag.E6 K)⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ = h
    rw [hPinv, ← mul_assoc, ← mul_assoc, hP2, one_mul, mul_assoc, hP2, mul_one]

variable [Finite k]

theorem exists_ringHom_apply_ne {q : ℕ} (hq : Nat.card k = q) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) : ∃ c : K, σ c ≠ c := by
  by_contra! h
  have hsurj : Function.Surjective (algebraMap k K) := fun c =>
    mem_range_algebraMap_of_pow_card_eq (by rw [hq, ← hσ, h c])
  have hle := Nat.card_le_card_of_surjective _ hsurj
  have hq2 : 1 < q := hq ▸ Finite.one_lt_card
  rw [hK, hq] at hle
  nlinarith

theorem mem_map_baseChangeGL_of_entrywise_fixed
    (hk : ringChar k = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card k)
    {h : ModGL TwistTag.E6.tag K} (hΓ : h ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K))
    (hfix : Units.map (entrywiseHom σ) h = h) :
    h ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) := by
  set L := AlgebraicClosure K
  obtain ⟨Fr, hFr⟩ := exists_frobenius_of_ringChar k L hk
  have hcomp : Fr.comp (algebraMap K L) = (algebraMap K L).comp σ := by
    ext c
    rw [RingHom.comp_apply, RingHom.comp_apply, hFr, hσ, map_pow]
  have hh' : baseChangeGL (algebraMap K L) h ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L) ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine ⟨baseChangeGL_mem_twistedFixedGroup _ hΓ, ?_⟩
    change baseChangeGL Fr (baseChangeGL (algebraMap K L) h) = baseChangeGL (algebraMap K L) h
    rw [baseChangeGL_baseChangeGL, hcomp, ← baseChangeGL_baseChangeGL]
    exact congrArg _ hfix
  rw [e6_frobenius_fixed_eq_map hk Fr hFr] at hh'
  obtain ⟨g, hg, hgh⟩ := hh'
  refine ⟨g, hg, baseChangeGL_injective (algebraMap K L) ?_⟩
  rw [baseChangeGL_baseChangeGL, ← IsScalarTower.algebraMap_eq, hgh]

variable [Finite K]

theorem canonicalGraphFixedSubgroup_graphFixedRootGroup
    {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hk2 : ringChar k = 2) :
    CanonicalGraphFixedSubgroup (graphFixedRootGroup TwistTag.E6 K σ)
      ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)))
      (diagramMap TwistTag.E6 K) := by
  have : Fintype k := Fintype.ofFinite k
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  set σE : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have hfixι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => by
    rw [hσ, ← map_pow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have e := graphFixedImageF4Equiv (algebraMap k K) h2
  refine canonicalGraphFixedSubgroup_of (map_conj_diagramMap_graphFixedRootGroup σE hσE hσσ)
    diagramMap_E6_mul_self ?_ (map_baseChangeGL_le_graphFixedRootGroup hfixι) ?_
    (isSimpleGroup_of_mulEquiv_adjointGroup_F4 hf hk e) (even_card_of_mulEquiv_adjointGroup_F4 h2 e)
    (center_graphFixedRootGroup_eq_bot hsurj)
  · obtain ⟨c, hc⟩ := exists_ringHom_apply_ne (σ := σ) hk hK hσ
    have hcmem : c ∈ orbitField TwistTag.E6 K σ ⟨0, by decide⟩ := by
      rw [mem_orbitField, show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide, pow_two,
        RingHom.coe_mul, Function.comp_apply, hσσ]
    refine ⟨(orbitX TwistTag.E6 K σ ⟨0, by decide⟩ ⟨c, hcmem⟩ : ModGL TwistTag.E6.tag K),
      graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _), ?_⟩
    rw [coe_orbitX_eq_orbitXProd TwistTag.E6 σ ⟨0, by decide⟩ ⟨c, hcmem⟩]
    refine diagramMap_conj_orbitXProd_ne ?_
    have h5 := orbitParam_pow TwistTag.E6 σ (a := ⟨0, by decide⟩) c (k := 1) (by decide)
    have h0 := orbitParam_orbitMin TwistTag.E6 σ ⟨0, by decide⟩ c
    rw [show (TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin ⟨0, by decide⟩) = ⟨5, by decide⟩ by
      decide, pow_one] at h5
    rw [show TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ by decide] at h0
    rw [h5, h0]
    exact hc
  · intro g hg
    rw [mul_inv_eq_iff_eq_mul]
    constructor
    · intro hPg
      have hΓσ := graphFixedRootGroup_le _ _ _ hg
      have hS : Units.map (entrywiseHom σ) g = g := by
        rw [← diagramMap_conj_eq_entrywise hσσ hΓσ, hPg, mul_inv_cancel_right]
      refine mem_map_baseChangeGL_of_entrywise_fixed hk2 (by rw [hk]; exact hσ)
        (mem_twistedFixedGroup_id_iff.2 ⟨hΓσ.1, hPg⟩) hS
    · rintro ⟨g', hg', rfl⟩
      exact (mem_twistedFixedGroup_id_iff.1 (baseChangeGL_mem_twistedFixedGroup _ hg')).2

end Twisted

theorem even_E6_twisted_E6_canonical_graph_fixed_subgroup
    (f : ℕ) (hf : 1 ≤ f) (k K : Type)
    [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (CanonicalGraphFixedSubgroup (adjointGroup TwistTag.E6.tag k)
        ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k)))
        (diagramMap TwistTag.E6 k) ∧
      ∃ e : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k)) ≃*
          adjointGroup Tag.F4 k,
        ∀ (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k))
          (x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k))),
          (x : ModGL TwistTag.E6.tag k) = baseChangeGL (RingHom.id k) g →
            (e x : ModGL Tag.F4 k) = e6FixedToF4 k g) ∧
    (CanonicalGraphFixedSubgroup (graphFixedRootGroup TwistTag.E6 K σ)
        ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)))
        (diagramMap TwistTag.E6 K) ∧
      ∃ e : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) ≃*
          adjointGroup Tag.F4 k,
        ∀ (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k))
          (x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
            (baseChangeGL (algebraMap k K))),
          (x : ModGL TwistTag.E6.tag K) = baseChangeGL (algebraMap k K) g →
            (e x : ModGL Tag.F4 k) = e6FixedToF4 k g) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  exact ⟨⟨canonicalGraphFixedSubgroup_adjointGroup k hf hk h2, graphFixedImageF4Equiv _ h2,
      graphFixedImageF4Equiv_apply _ h2⟩,
    ⟨canonicalGraphFixedSubgroup_graphFixedRootGroup hf hk hK hσ hk2, graphFixedImageF4Equiv _ h2,
      graphFixedImageF4Equiv_apply _ h2⟩⟩

end CFSG.LieType.Chevalley
