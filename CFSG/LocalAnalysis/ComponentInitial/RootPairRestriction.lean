module

public import CFSG.LocalAnalysis.ComponentInitial.GroupOuter
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

variable {M : Type*} [Group M]

@[expose] def pairAutSubgroup (U V : Subgroup M) : Subgroup (MulAut M) where
  carrier := {α | U.map α.toMonoidHom = U ∧ V.map α.toMonoidHom = V}
  one_mem' := ⟨by ext x; simp, by ext x; simp⟩
  mul_mem' {α β} hα hβ := by
    refine ⟨?_, ?_⟩
    · rw [show (α * β).toMonoidHom = α.toMonoidHom.comp β.toMonoidHom from rfl,
        ← Subgroup.map_map, hβ.1, hα.1]
    · rw [show (α * β).toMonoidHom = α.toMonoidHom.comp β.toMonoidHom from rfl,
        ← Subgroup.map_map, hβ.2, hα.2]
  inv_mem' {α} hα := by
    have key : ∀ X : Subgroup M, X.map α.toMonoidHom = X → X.map α⁻¹.toMonoidHom = X := by
      intro X hX
      ext x
      rw [Subgroup.mem_map_equiv]
      change α x ∈ X ↔ x ∈ X
      rw [← hX, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, hX]
    exact ⟨key U hα.1, key V hα.2⟩

theorem apply_mem_of_mem_pairAut {U V : Subgroup M} {α : MulAut M}
    (hα : α ∈ pairAutSubgroup U V) {u : M} (hu : u ∈ U) : α u ∈ U := by
  rw [← hα.1]
  exact Subgroup.mem_map_of_mem _ hu

theorem apply_mem_of_mem_pairAut_right {U V : Subgroup M} {α : MulAut M}
    (hα : α ∈ pairAutSubgroup U V) {v : M} (hv : v ∈ V) : α v ∈ V := by
  rw [← hα.2]
  exact Subgroup.mem_map_of_mem _ hv

@[expose] noncomputable def pairAutRestrict (U V : Subgroup M) :
    pairAutSubgroup U V →* MulAut U where
  toFun α :=
    { toFun := fun u => ⟨α.1 (u : M), apply_mem_of_mem_pairAut α.2 u.2⟩
      invFun := fun u => ⟨α.1⁻¹ (u : M), apply_mem_of_mem_pairAut (inv_mem α.2) u.2⟩
      left_inv := fun u => Subtype.ext (α.1.symm_apply_apply (u : M))
      right_inv := fun u => Subtype.ext (α.1.apply_symm_apply (u : M))
      map_mul' := fun u u' => Subtype.ext (map_mul α.1 (u : M) (u' : M)) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

section Points

variable {Ω : Type*} [MulAction M Ω] {p : ℕ}

theorem mulAut_smul_smul_sylow' (α : MulAut M) (g : M) (P : Sylow p M) :
    α • (g • P) = (α g) • (α • P) := by
  refine Sylow.ext (Subgroup.ext fun x => ?_)
  rw [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul,
    Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists,
    Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy
    refine ⟨α z, (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨z, hz, rfl⟩, ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply, map_mul, map_inv]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy
    refine ⟨g * z * g⁻¹, (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨z, hz, rfl⟩, ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply, map_mul, map_inv]

theorem coe_smul_sylow' (g : M) (P : Sylow p M) :
    ((g • P : Sylow p M) : Subgroup M) = (P : Subgroup M).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem coe_mulAut_smul_sylow' (α : MulAut M) (P : Sylow p M) :
    ((α • P : Sylow p M) : Subgroup M) = (P : Subgroup M).map α.toMonoidHom := by
  ext x
  rw [Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

variable {ξ : Ω} {U : Sylow p M}

theorem eq_of_forall_smul_eq [Finite Ω] (hΩ : 3 ≤ Nat.card Ω)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup M), (u : M) • ω = ω')
    {ω : Ω} (hω : ∀ u ∈ (U : Subgroup M), u • ω = ω) : ω = ξ := by
  by_contra hne
  obtain ⟨ω', hω'ξ, hω'ω⟩ : ∃ ω' : Ω, ω' ≠ ξ ∧ ω' ≠ ω := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set Ω) ⊆ {ξ, ω} := fun x _ => by
      by_cases hx : x = ξ
      · exact Or.inl hx
      · exact Or.inr (h x hx)
    have h2 : (Set.univ : Set Ω).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by
        refine (Set.ncard_insert_le ξ {ω}).trans ?_
        rw [Set.ncard_singleton])
    rw [Set.ncard_univ] at h2
    omega
  obtain ⟨u, hu⟩ := htr ω ω' hne hω'ξ
  exact hω'ω (hu.symm.trans (hω u u.2))

variable [Finite Ω] (hΩ : 3 ≤ Nat.card Ω)
  (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup M), (u : M) • ω = ω')
  (hUξ : (U : Subgroup M) ≤ MulAction.stabilizer M ξ)
  (hUn : ((U : Subgroup M).subgroupOf (MulAction.stabilizer M ξ)).Normal)

include hΩ htr hUξ hUn in
theorem normalizer_eq_stabilizer :
    Subgroup.normalizer ((U : Subgroup M) : Set M) = MulAction.stabilizer M ξ := by
  apply le_antisymm
  · intro g hg
    rw [MulAction.mem_stabilizer_iff]
    refine eq_of_forall_smul_eq hΩ htr fun u hu => ?_
    have h1 : g⁻¹ * u * g ∈ (U : Subgroup M) := (Subgroup.mem_normalizer_iff''.1 hg u).1 hu
    have h2 : (g⁻¹ * u * g) • ξ = ξ := hUξ h1
    calc u • g • ξ = g • (g⁻¹ * u * g) • ξ := by
          rw [smul_smul, smul_smul]; group
      _ = g • ξ := by rw [h2]
  · intro g hg
    have hconj := (Subgroup.normal_subgroupOf_iff hUξ).1 hUn
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hconj h g hh hg, fun hh => ?_⟩
    have := hconj _ g⁻¹ hh (inv_mem hg)
    simpa [mul_assoc] using this

include hΩ htr hUξ hUn in
theorem smul_sylow_eq_iff {g h : M} : g • U = h • U ↔ g • ξ = h • ξ := by
  have hN := normalizer_eq_stabilizer hΩ htr hUξ hUn
  constructor
  · intro e
    have h1 : (h⁻¹ * g) • U = U := by rw [mul_smul, e, inv_smul_smul]
    have h2 : h⁻¹ * g ∈ MulAction.stabilizer M ξ := by
      rw [← hN]
      exact (Sylow.smul_eq_iff_mem_normalizer).1 h1
    have h3 : (h⁻¹ * g) • ξ = ξ := h2
    rw [mul_smul, inv_smul_eq_iff] at h3
    exact h3
  · intro e
    have h1 : (h⁻¹ * g) • ξ = ξ := by rw [mul_smul, e, inv_smul_smul]
    have h2 : h⁻¹ * g ∈ Subgroup.normalizer ((U : Subgroup M) : Set M) := by
      rw [hN]
      exact h1
    have h3 := (Sylow.smul_eq_iff_mem_normalizer).2 h2
    rw [mul_smul, inv_smul_eq_iff] at h3
    exact h3

variable [MulAction.IsPretransitive M Ω]

variable (ξ U) in
@[expose] noncomputable def sylowPoint (ω : Ω) : Sylow p M :=
  (MulAction.exists_smul_eq M ξ ω).choose • U

include hΩ htr hUξ hUn in
theorem sylowPoint_eq {g : M} {ω : Ω} (hg : g • ξ = ω) : sylowPoint ξ U ω = g • U :=
  (smul_sylow_eq_iff hΩ htr hUξ hUn).2 ((MulAction.exists_smul_eq M ξ ω).choose_spec.trans hg.symm)

include hΩ htr hUξ hUn in
theorem sylowPoint_smul (k : M) (ω : Ω) : sylowPoint ξ U (k • ω) = k • sylowPoint ξ U ω := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq M ξ ω
  rw [sylowPoint_eq hΩ htr hUξ hUn (rfl : g • ξ = g • ξ),
    sylowPoint_eq hΩ htr hUξ hUn (show (k * g) • ξ = k • g • ξ from mul_smul k g ξ), mul_smul]

include hΩ htr hUξ hUn in
theorem sylowPoint_self : sylowPoint ξ U ξ = U := by
  rw [sylowPoint_eq hΩ htr hUξ hUn (one_smul M ξ), one_smul]

variable [Fact p.Prime] [Finite M]

include hΩ htr hUξ hUn in
theorem sylowPoint_bijective : Function.Bijective (sylowPoint ξ U (Ω := Ω)) := by
  refine ⟨fun ω ω' h => ?_, fun S => ?_⟩
  · obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq M ξ ω
    obtain ⟨g', rfl⟩ := MulAction.exists_smul_eq M ξ ω'
    rw [sylowPoint_eq hΩ htr hUξ hUn rfl, sylowPoint_eq hΩ htr hUξ hUn rfl] at h
    exact (smul_sylow_eq_iff hΩ htr hUξ hUn).1 h
  · obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq M U S
    exact ⟨g • ξ, sylowPoint_eq hΩ htr hUξ hUn rfl⟩

@[expose] noncomputable def sylowPointEquiv : Ω ≃ Sylow p M :=
  Equiv.ofBijective _ (sylowPoint_bijective hΩ htr hUξ hUn)

@[expose] noncomputable def sylowPointPerm (α : MulAut M) : Equiv.Perm Ω :=
  ((sylowPointEquiv hΩ htr hUξ hUn).trans (MulAction.toPerm α)).trans
    (sylowPointEquiv hΩ htr hUξ hUn).symm

theorem sylowPointEquiv_apply (ω : Ω) :
    sylowPointEquiv hΩ htr hUξ hUn ω = sylowPoint ξ U ω :=
  rfl

theorem apply_sylowPointPerm (α : MulAut M) (ω : Ω) :
    sylowPointEquiv hΩ htr hUξ hUn (sylowPointPerm hΩ htr hUξ hUn α ω) =
      α • sylowPointEquiv hΩ htr hUξ hUn ω := by
  simp [sylowPointPerm]

theorem sylowPointPerm_smul (α : MulAut M) (g : M) (ω : Ω) :
    sylowPointPerm hΩ htr hUξ hUn α (g • ω) = α g • sylowPointPerm hΩ htr hUξ hUn α ω := by
  apply (sylowPointEquiv hΩ htr hUξ hUn).injective
  rw [apply_sylowPointPerm, sylowPointEquiv_apply, sylowPointEquiv_apply,
    sylowPoint_smul hΩ htr hUξ hUn, sylowPoint_smul hΩ htr hUξ hUn,
    mulAut_smul_smul_sylow', ← sylowPointEquiv_apply hΩ htr hUξ hUn, ← apply_sylowPointPerm]
  rfl

theorem sylowPointPerm_mul (α α' : MulAut M) :
    sylowPointPerm hΩ htr hUξ hUn (α * α') =
      sylowPointPerm hΩ htr hUξ hUn α * sylowPointPerm hΩ htr hUξ hUn α' := by
  refine Equiv.ext fun ω => (sylowPointEquiv hΩ htr hUξ hUn).injective ?_
  rw [Equiv.Perm.mul_apply, apply_sylowPointPerm, apply_sylowPointPerm, apply_sylowPointPerm,
    mul_smul]

theorem sylowPointPerm_conj (g : M) (ω : Ω) :
    sylowPointPerm hΩ htr hUξ hUn (MulAut.conj g) ω = g • ω := by
  apply (sylowPointEquiv hΩ htr hUξ hUn).injective
  rw [apply_sylowPointPerm, sylowPointEquiv_apply, sylowPointEquiv_apply,
    sylowPoint_smul hΩ htr hUξ hUn]
  rfl

theorem sylowPointPerm_eq_iff (α : MulAut M) (ω : Ω) :
    sylowPointPerm hΩ htr hUξ hUn α ω = ω ↔
      ((sylowPoint ξ U ω : Sylow p M) : Subgroup M).map α.toMonoidHom = sylowPoint ξ U ω := by
  have h := apply_sylowPointPerm hΩ htr hUξ hUn α ω
  rw [sylowPointEquiv_apply, sylowPointEquiv_apply] at h
  rw [← coe_mulAut_smul_sylow']
  constructor
  · intro e
    rw [← h, e]
  · intro e
    apply (sylowPointEquiv hΩ htr hUξ hUn).injective
    rw [sylowPointEquiv_apply, sylowPointEquiv_apply, h]
    exact Sylow.ext e

include hΩ hUξ hUn in
theorem large_Ree_root_pair_restriction
    (hreg : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃! u : (U : Subgroup M), (u : M) • ω = ω')
    (w : M) (hw : w • ξ ≠ ξ)
    (hgen : (U : Subgroup M) ⊔ (U : Subgroup M).map (MulAut.conj w).toMonoidHom = ⊤) :
    Function.Injective (pairAutRestrict (U : Subgroup M)
      ((U : Subgroup M).map (MulAut.conj w).toMonoidHom)) ∧
    (∀ α : MulAut M, ∃ g : M, ∃ β ∈ pairAutSubgroup (U : Subgroup M)
      ((U : Subgroup M).map (MulAut.conj w).toMonoidHom), α = MulAut.conj g * β) ∧
    ∀ d : ℕ, derivedSeries (MulAut (U : Subgroup M)) d = ⊥ → derivedSeries (Outer M) d = ⊥ := by
  have htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup M), (u : M) • ω = ω' :=
    fun ω ω' h1 h2 => (hreg ω ω' h1 h2).exists
  set V := (U : Subgroup M).map (MulAut.conj w).toMonoidHom with hV
  set π := sylowPointPerm hΩ htr hUξ hUn (U := U) with hπ
  have hξ : sylowPoint ξ U ξ = U := sylowPoint_self hΩ htr hUξ hUn
  have hη : ((sylowPoint ξ U (w • ξ) : Sylow p M) : Subgroup M) = V := by
    rw [sylowPoint_eq hΩ htr hUξ hUn rfl, coe_smul_sylow']
  have hmemC : ∀ β : MulAut M, π β ξ = ξ → π β (w • ξ) = w • ξ →
      β ∈ pairAutSubgroup (U : Subgroup M) V := by
    intro β h1 h2
    rw [sylowPointPerm_eq_iff, hξ] at h1
    rw [sylowPointPerm_eq_iff, hη] at h2
    exact ⟨h1, h2⟩
  have hfixC : ∀ β ∈ pairAutSubgroup (U : Subgroup M) V, π β ξ = ξ ∧ π β (w • ξ) = w • ξ := by
    intro β hβ
    refine ⟨(sylowPointPerm_eq_iff _ _ _ _ β ξ).2 ?_, (sylowPointPerm_eq_iff _ _ _ _ β _).2 ?_⟩
    · rw [hξ]
      exact hβ.1
    · rw [hη]
      exact hβ.2
  have hInnC : ∀ α : MulAut M, ∃ g : M, ∃ β ∈ pairAutSubgroup (U : Subgroup M) V,
      α = MulAut.conj g * β := by
    intro α
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq M ξ (π α ξ)
    have hne : h⁻¹ • π α (w • ξ) ≠ ξ := by
      intro he
      rw [inv_smul_eq_iff, hh] at he
      exact hw ((π α).injective he)
    obtain ⟨u, hu, -⟩ := hreg (w • ξ) (h⁻¹ • π α (w • ξ)) hw hne
    set g := h * (u : M) with hg
    have hgξ : g • ξ = π α ξ := by
      rw [hg, mul_smul, show (u : M) • ξ = ξ from hUξ u.2, hh]
    have hgη : g • (w • ξ) = π α (w • ξ) := by
      rw [hg, mul_smul, hu, smul_inv_smul]
    have hπβ : ∀ ω, π ((MulAut.conj g)⁻¹ * α) ω = g⁻¹ • π α ω := fun ω => by
      rw [hπ, sylowPointPerm_mul, Equiv.Perm.mul_apply, ← map_inv, sylowPointPerm_conj]
    refine ⟨g, (MulAut.conj g)⁻¹ * α, hmemC _ ?_ ?_, (mul_inv_cancel_left _ _).symm⟩
    · rw [hπβ, ← hgξ, inv_smul_smul]
    · rw [hπβ, ← hgη, inv_smul_smul]
  have hinj : Function.Injective (pairAutRestrict (U : Subgroup M) V) := by
    rw [injective_iff_map_eq_one]
    intro β hβ
    have hU1 : ∀ u ∈ (U : Subgroup M), (β : MulAut M) u = u := fun u hu => by
      have := congrArg (fun e : MulAut (U : Subgroup M) => ((e ⟨u, hu⟩ : U) : M)) hβ
      exact this
    obtain ⟨h1, h2⟩ := hfixC β β.2
    have hπ1 : ∀ ω, π β ω = ω := by
      intro ω
      by_cases hωξ : ω = ξ
      · rw [hωξ, h1]
      · obtain ⟨u, hu, -⟩ := hreg (w • ξ) ω hw hωξ
        rw [← hu, sylowPointPerm_smul, h2, hU1 _ u.2]
    have hact : ∀ (g : M) (ω : Ω), (β : MulAut M) g • ω = g • ω := fun g ω => by
      have := sylowPointPerm_smul hΩ htr hUξ hUn (β : MulAut M) g ω
      rw [hπ1, hπ1] at this
      exact this.symm
    have hfaith : ∀ v ∈ V, (∀ ω : Ω, v • ω = ω) → v = 1 := by
      rintro _ ⟨u, hu, rfl⟩ hv
      have hu' : u = 1 := by
        have h3 : u • (w • ξ) = w • ξ := by
          have := hv (w • (w • ξ))
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_smul,
            inv_smul_smul] at this
          exact smul_left_cancel w this
        obtain ⟨u₀, -, huniq⟩ := hreg (w • ξ) (w • ξ) hw hw
        have e1 := huniq ⟨u, hu⟩ h3
        have e2 := huniq 1 (one_smul M _)
        exact congrArg Subtype.val (e1.trans e2.symm)
      simp [hu']
    have hV1 : ∀ v ∈ V, (β : MulAut M) v = v := fun v hv => by
      have hαv : (β : MulAut M) v ∈ V := apply_mem_of_mem_pairAut_right β.2 hv
      have h4 : ((β : MulAut M) v)⁻¹ * v = 1 := hfaith _ (mul_mem (inv_mem hαv) hv) fun ω => by
        rw [mul_smul, inv_smul_eq_iff, hact]
      rw [inv_mul_eq_one] at h4
      exact h4
    have hall : ∀ g : M, (β : MulAut M) g = g := by
      intro g
      have hle : (U : Subgroup M) ⊔ V ≤ ((β : MulAut M).toMonoidHom).eqLocus (MonoidHom.id M) :=
        sup_le (fun u hu => hU1 u hu) (fun v hv => hV1 v hv)
      rw [hgen] at hle
      exact hle (Subgroup.mem_top g)
    exact Subtype.ext (MulEquiv.ext hall)
  refine ⟨hinj, hInnC, fun d hd => ?_⟩
  have hC : derivedSeries (pairAutSubgroup (U : Subgroup M) V) d = ⊥ := by
    have := map_derivedSeries_le_derivedSeries (pairAutRestrict (U : Subgroup M) V) d
    rw [hd, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hinj] at this
    exact this
  set q : pairAutSubgroup (U : Subgroup M) V →* Outer M :=
    (QuotientGroup.mk' (inner M)).comp (pairAutSubgroup (U : Subgroup M) V).subtype with hq
  have hqs : Function.Surjective q := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner M) x
    obtain ⟨g, β, hβ, rfl⟩ := hInnC α
    refine ⟨⟨β, hβ⟩, ?_⟩
    have h1 : QuotientGroup.mk' (inner M) (MulAut.conj g) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact ⟨g, rfl⟩
    change QuotientGroup.mk' (inner M) β = QuotientGroup.mk' (inner M) (MulAut.conj g * β)
    rw [map_mul, h1, one_mul]
  rw [← map_derivedSeries_eq hqs, hC, Subgroup.map_bot]

end Points

end CFSG.LocalAnalysis.ComponentInitial
