module

public import CFSG.LieType.Chevalley.SteinbergBNDiagonalFieldSemilinear
public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.LieType.Chevalley.ParabolicDiagonalFieldNormalizersFixed

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  RootWeight

section ConjugateRadical

variable {C : Type*} [Group C]

theorem mem_map_center_subtype_iff {U : Subgroup C} {z : C} :
    z ∈ (Subgroup.center U).map U.subtype ↔ z ∈ U ∧ ∀ u ∈ U, z * u = u * z := by
  constructor
  · rintro ⟨⟨z, hzU⟩, hz, rfl⟩
    refine ⟨hzU, fun u hu => ?_⟩
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨u, hu⟩)
    exact h.symm
  · rintro ⟨hzU, hz⟩
    refine ⟨⟨z, hzU⟩, Subgroup.mem_center_iff.2 fun u => Subtype.ext (hz u u.2).symm, rfl⟩

theorem conj_inv_mul_conj_mul_conj (g z : C) :
    (MulAut.conj g)⁻¹ * MulAut.conj z * MulAut.conj g = MulAut.conj (g⁻¹ * z * g) := by
  rw [← map_inv, ← map_mul, ← map_mul]

theorem pointwise_stabilizer_map_conj {A : Subgroup (MulAut C)}
    (hInn : (MulAut.conj : C →* MulAut C).range ≤ A) {R : Subgroup C}
    (hR : ∀ α : MulAut C, (α ∈ A ∧ ∀ q ∈ R, α q = q) ↔
      α ∈ ((Subgroup.center R).map R.subtype).map MulAut.conj) (g : C) (α : MulAut C) :
    (α ∈ A ∧ ∀ u ∈ R.map (MulAut.conj g).toMonoidHom, α u = u) ↔
      α ∈ ((Subgroup.center (R.map (MulAut.conj g).toMonoidHom)).map
        (R.map (MulAut.conj g).toMonoidHom).subtype).map MulAut.conj := by
  set U := R.map (MulAut.conj g).toMonoidHom
  have hU : ∀ u, u ∈ U ↔ g⁻¹ * u * g ∈ R := fun u => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  set α' := (MulAut.conj g)⁻¹ * α * MulAut.conj g
  have hα' : ∀ q, α' q = g⁻¹ * α (g * q * g⁻¹) * g := fun q => by
    simp [α', MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
  have hgA : MulAut.conj g ∈ A := hInn ⟨g, rfl⟩
  have hA : α ∈ A ↔ α' ∈ A := by
    constructor
    · intro h
      exact mul_mem (mul_mem (inv_mem hgA) h) hgA
    · intro h
      have e : α = MulAut.conj g * α' * (MulAut.conj g)⁻¹ := by
        simp only [α']
        group
      rw [e]
      exact mul_mem (mul_mem hgA h) (inv_mem hgA)
  have hfix : (∀ u ∈ U, α u = u) ↔ ∀ q ∈ R, α' q = q := by
    constructor
    · intro h q hq
      have hu : g * q * g⁻¹ ∈ U := (hU _).2 (by simpa [mul_assoc] using hq)
      rw [hα', h _ hu]
      group
    · intro h u hu
      have hq := h _ ((hU u).1 hu)
      rw [hα'] at hq
      have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
      rw [e] at hq
      calc α u = g * (g⁻¹ * α u * g) * g⁻¹ := by group
        _ = u := by rw [hq]; group
  have hZ : α ∈ ((Subgroup.center U).map U.subtype).map MulAut.conj ↔
      α' ∈ ((Subgroup.center R).map R.subtype).map MulAut.conj := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzU, hzc⟩ := mem_map_center_subtype_iff.1 hz
      refine ⟨g⁻¹ * z * g, mem_map_center_subtype_iff.2 ⟨(hU z).1 hzU, fun q hq => ?_⟩,
        (conj_inv_mul_conj_mul_conj g z).symm⟩
      have hu : g * q * g⁻¹ ∈ U := (hU _).2 (by simpa [mul_assoc] using hq)
      have h := hzc _ hu
      calc g⁻¹ * z * g * q = g⁻¹ * (z * (g * q * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * q * g⁻¹) * z) * g := by rw [h]
        _ = q * (g⁻¹ * z * g) := by group
    · rintro ⟨w, hw, hwα⟩
      obtain ⟨hwR, hwc⟩ := mem_map_center_subtype_iff.1 hw
      refine ⟨g * w * g⁻¹, mem_map_center_subtype_iff.2 ⟨(hU _).2 (by simpa [mul_assoc] using hwR),
        fun u hu => ?_⟩, ?_⟩
      · have h := hwc _ ((hU u).1 hu)
        calc g * w * g⁻¹ * u = g * (w * (g⁻¹ * u * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * u * g) * w) * g⁻¹ := by rw [h]
          _ = u * (g * w * g⁻¹) := by group
      · have e : α = MulAut.conj g * α' * (MulAut.conj g)⁻¹ := by
          simp only [α']
          group
        rw [e, ← hwα, ← map_inv, ← map_mul, ← map_mul]
  rw [hA, hfix, hZ]
  exact hR α'

end ConjugateRadical

namespace RootWeightDatum

variable {K : Type} [Field K]

@[expose] def radicalIn
    (D : RootWeightDatum K) (J : Set (Fin D.rank)) : Subgroup D.group :=
  (D.radical J).subgroupOf D.group

@[expose] def actors
    : (D : RootWeightDatum K) → Subgroup (MulAut D.group)
  | ordinary τ => diagonalFieldActors τ K
  | fixed t σ _ => fixedDiagonalFieldActors t K σ

variable (D : RootWeightDatum K)

theorem parabolic_le_normalizer_radical
    (J : Set (Fin D.rank)) :
    D.parabolic J ≤ Subgroup.normalizer (D.radical J : Set (ModGL D.tag K)) := fun x hx =>
  Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => D.conj_mem_radical J hx hy, fun hy => by
    have h := D.conj_mem_radical J (inv_mem hx) hy
    rwa [inv_inv, show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h⟩

theorem exists_actor_decomp
    {α : MulAut D.group} (hα : α ∈ D.actors) :
    ∃ c ∈ D.group, ∃ (δ : K ≃+* K) (a : Fin D.tag.rank → Kˣ),
      (∀ x : D.group, (α x : ModGL D.tag K) = c * (rootDiagUnit D.tag a *
        Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit D.tag a)⁻¹) * c⁻¹) ∧
      (∀ x, rootDiagUnit D.tag a * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit D.tag a)⁻¹ ∈ D.group ↔ x ∈ D.group) ∧
      ∀ J, ∀ x, rootDiagUnit D.tag a * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit D.tag a)⁻¹ ∈ D.radical J ↔ x ∈ D.radical J := by
  cases D with
  | ordinary τ =>
    obtain ⟨c, hc, a, δ, hαx⟩ := ((Chevalley_diagonal_field_actor_data.1 τ K).1 α).1 hα
    have hconj := chevalley_root_character_and_field_conjugation τ K
    refine ⟨c, hc, δ, a, fun x => (hαx x).trans (by simp only [mul_assoc]; rfl),
      diag_entrywise_mem_iff δ a
      (hconj.2.2.2.2.1 δ).1 (hconj.2.2.2.1 a).1, fun J => diag_entrywise_mem_iff δ a
      (map_rootSpan_of_forall fun β _ => map_entrywise_rootSubgroup δ β)
      (map_rootSpan_of_forall fun β hβ => map_conj_rootDiagUnit_rootSubgroup a hβ.1.1)⟩
  | fixed t σ hσ =>
    obtain ⟨c, hc, a, ha, δ, hδσ, hαx⟩ := ((Chevalley_diagonal_field_actor_data.2 t K σ).1 α).1 hα
    have hδ : ∀ x, δ (σ.toRingHom x) = σ.toRingHom (δ x) := fun x =>
      congrArg (fun φ : K ≃+* K => φ x) hδσ
    refine ⟨c, hc, δ, a, fun x => (hαx x).trans (by simp only [mul_assoc]; rfl),
      diag_entrywise_mem_iff δ a
      (map_units_map_entrywiseHom_graphFixedRootGroup (σ := σ.toRingHom) hδ)
      (map_conj_rootDiagUnit_graphFixedRootGroup (σ := σ.toRingHom) ha), fun J => ?_⟩
    refine diag_entrywise_mem_iff δ a ?_ ?_
    · change (parabolicRadical t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom).map
        _ = parabolicRadical t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom
      rw [Subgroup.map_inf_eq _ _ _ (exactEntrywiseAut t.tag δ).injective,
        map_units_map_entrywiseHom_twistedFixedGroup (σ := σ.toRingHom) hδ,
        show (parabolicRadical t.tag K (t.orbitUnion J)).map
            (Units.map (entrywiseHom δ.toRingHom)) = parabolicRadical t.tag K (t.orbitUnion J) from
            map_rootSpan_of_forall fun β _ => map_entrywise_rootSubgroup δ β]
    · change (parabolicRadical t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom).map
        _ = parabolicRadical t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
        map_conj_eq_of_mem_normalizer (rootDiagUnit_mem_normalizer_twistedFixedGroup
          (σ := σ.toRingHom) ha),
        show (parabolicRadical t.tag K (t.orbitUnion J)).map
            (MulAut.conj (rootDiagUnit t.tag a)).toMonoidHom =
          parabolicRadical t.tag K (t.orbitUnion J) from
            map_rootSpan_of_forall fun β hβ => map_conj_rootDiagUnit_rootSubgroup a hβ.1.1]

theorem conj_range_le_actors
    : (MulAut.conj : D.group →* MulAut D.group).range ≤ D.actors := by
  cases D with
  | ordinary τ => exact (Chevalley_diagonal_field_actor_data.1 τ K).2.2
  | fixed t σ hσ => exact (Chevalley_diagonal_field_actor_data.2 t K σ).2.2

theorem radical_facts
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] {J : Set (Fin D.rank)}
    (hJ : J ≠ Set.univ) :
    Subgroup.center D.group = ⊥ ∧ D.radicalIn J ≠ ⊥ ∧ IsPGroup p (D.radicalIn J) ∧
      ∀ α : MulAut D.group, (α ∈ D.actors ∧ ∀ q ∈ D.radicalIn J, α q = q) ↔
        α ∈ ((Subgroup.center (D.radicalIn J)).map (D.radicalIn J).subtype).map MulAut.conj := by
  cases D with
  | ordinary τ =>
    obtain ⟨hZ, hne, hp, hall, -⟩ :=
      exact_parabolic_diagonal_field_normalizers_characteristic_p_ordinary (p := p) τ K hJ
    exact ⟨hZ, hne, hp, hall⟩
  | fixed t σ hσ =>
    obtain ⟨hZ, hne, hp, hall, -⟩ :=
      exact_parabolic_diagonal_field_normalizers_characteristic_p_fixed (p := p) t K σ hσ hJ
    exact ⟨hZ, hne, hp, hall⟩

theorem root_p_subgroup_diagonal_field_invariant_radical
    [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] :
    Finite D.group ∧ Subgroup.center D.group = ⊥ ∧
    ∀ Q : Subgroup D.group, Q ≠ ⊥ → IsPGroup p Q →
      ∃ (g : D.group) (J : Set (Fin D.rank)) (U : Subgroup D.group), J ≠ Set.univ ∧
        U = (D.radicalIn J).map (MulAut.conj g).toMonoidHom ∧ U ≠ ⊥ ∧ IsPGroup p U ∧
        setwiseStabilizer D.actors Q ≤ setwiseStabilizer D.actors U ∧
        (∀ α : MulAut D.group, (α ∈ D.actors ∧ ∀ u ∈ U, α u = u) ↔
          α ∈ ((Subgroup.center U).map U.subtype).map MulAut.conj) ∧
        ((Subgroup.center U).map U.subtype).map MulAut.conj ≤ U.map MulAut.conj := by
  have : Finite (ModGL D.tag K) := finite_modGL
  have h0 : (∅ : Set (Fin D.rank)) ≠ Set.univ := fun h => by
    have hmem := Set.mem_univ (⟨0, D.rank_pos⟩ : Fin D.rank)
    rw [← h] at hmem
    exact hmem
  refine ⟨inferInstance, (D.radical_facts p h0).1, fun Q hQ hQp => ?_⟩
  set Q' := Q.map D.group.subtype with hQ'
  have hQ'G : Q' ≤ D.group := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hQ'1 : Q' ≠ ⊥ := fun h => hQ (by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : ModGL D.tag K) ∈ Q' := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext hx'))
  obtain ⟨g, hg, J, hJ, htrans⟩ := D.exists_conj_radical_invariant p D.radical
    D.parabolic_le_normalizer_radical hQ'G (hQp.map _) hQ'1
  obtain ⟨-, hRne, hRp, hRpt⟩ := D.radical_facts p hJ
  set g' : D.group := ⟨g, hg⟩
  set U := (D.radicalIn J).map (MulAut.conj g').toMonoidHom with hU
  have hUmem : ∀ u : D.group, u ∈ U ↔ g'⁻¹ * u * g' ∈ D.radicalIn J := fun u => by
    rw [hU, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  refine ⟨g', J, U, hJ, rfl, ?_, hRp.map _, ?_,
    pointwise_stabilizer_map_conj D.conj_range_le_actors hRpt g',
    Subgroup.map_mono (Subgroup.map_subtype_le _)⟩
  ·
    intro h
    apply hRne
    rw [eq_bot_iff]
    intro r hr
    have hr' : (MulAut.conj g').toMonoidHom r ∈ U := ⟨r, hr, rfl⟩
    rw [h, Subgroup.mem_bot] at hr'
    exact Subgroup.mem_bot.2 ((MulAut.conj g').injective (hr'.trans (map_one _).symm))
  ·
    rintro α ⟨hα, hαQ⟩
    refine ⟨hα, ?_⟩
    obtain ⟨c, hc, δ, a, hαx, hβG, hβR⟩ := D.exists_actor_decomp hα
    have hβQ : ∀ x, x ∈ Q' ↔ ∃ q ∈ Q', c * (rootDiagUnit D.tag a *
        Units.map (entrywiseHom δ.toRingHom) q * (rootDiagUnit D.tag a)⁻¹) * c⁻¹ = x := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← hαQ] at hy
        obtain ⟨y', hy', rfl⟩ := hy
        exact ⟨y', ⟨y', hy', rfl⟩, by
          simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
          exact (hαx y').symm⟩
      · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
        refine ⟨α y', ?_, by
          simp only [Subgroup.coe_subtype]
          exact hαx y'⟩
        rw [← hαQ]
        exact ⟨y', hy', rfl⟩
    have hle : U.map α.toMonoidHom ≤ U := by
      rintro _ ⟨u, ⟨r, hr, rfl⟩, rfl⟩
      obtain ⟨y, hy, hyx⟩ := htrans c hc δ a hβG (fun x hx => (hβR J x).2 hx) hβQ
        (r : ModGL D.tag K) (Subgroup.mem_subgroupOf.1 hr)
      rw [hUmem, RootWeightDatum.radicalIn, Subgroup.mem_subgroupOf]
      have e : ((α ((MulAut.conj g').toMonoidHom r) : D.group) : ModGL D.tag K) = g * y * g⁻¹ := by
        rw [MulEquiv.coe_toMonoidHom, hαx]
        change c * (_ * Units.map _ (g * (r : ModGL D.tag K) * g⁻¹) * _) * c⁻¹ = g * y * g⁻¹
        rw [← hyx]
        rfl
      have e2 : ((g'⁻¹ * α ((MulAut.conj g').toMonoidHom r) * g' : D.group) : ModGL D.tag K) =
          y := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, e]
        change g⁻¹ * (g * y * g⁻¹) * g = y
        group
      change ((g'⁻¹ * α ((MulAut.conj g').toMonoidHom r) * g' : D.group) : ModGL D.tag K) ∈ _
      rw [e2]
      exact hy
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (f := α.toMonoidHom) (K := U) α.injective).ge

end RootWeightDatum

end CFSG.LieType.Chevalley
