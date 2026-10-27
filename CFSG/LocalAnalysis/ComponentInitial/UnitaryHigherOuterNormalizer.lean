module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPointNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

section Transport

variable {G G' Ω Ω' : Type*} [Group G] [Group G']

theorem map_range_permCongrHom (j : Ω ≃ Ω') (β : G ≃* G') {ρ : G →* Equiv.Perm Ω}
    {ρ' : G' →* Equiv.Perm Ω'} (hj : ∀ g, j.permCongr (ρ g) = ρ' (β g)) :
    ρ.range.map j.permCongrHom.toMonoidHom = ρ'.range := by
  ext y
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨β g, (hj g).symm⟩
  · rintro ⟨g', rfl⟩
    refine ⟨ρ (β.symm g'), ⟨_, rfl⟩, ?_⟩
    change j.permCongr (ρ (β.symm g')) = ρ' g'
    rw [hj, MulEquiv.apply_symm_apply]

theorem nonempty_normalizerQuotient_mulEquiv (j : Ω ≃ Ω') (β : G ≃* G')
    {ρ : G →* Equiv.Perm Ω} {ρ' : G' →* Equiv.Perm Ω'}
    (hj : ∀ g, j.permCongr (ρ g) = ρ' (β g)) :
    Nonempty (Subgroup.normalizer (ρ.range : Set (Equiv.Perm Ω)) ⧸
        ρ.range.subgroupOf (Subgroup.normalizer (ρ.range : Set (Equiv.Perm Ω))) ≃*
      Subgroup.normalizer (ρ'.range : Set (Equiv.Perm Ω')) ⧸
        ρ'.range.subgroupOf (Subgroup.normalizer (ρ'.range : Set (Equiv.Perm Ω')))) := by
  set Φ := j.permCongrHom with hΦ
  have hrange := map_range_permCongrHom j β hj
  have hnorm : (Subgroup.normalizer (ρ.range : Set (Equiv.Perm Ω))).map Φ.toMonoidHom =
      Subgroup.normalizer (ρ'.range : Set (Equiv.Perm Ω')) := by
    rw [Subgroup.map_equiv_normalizer_eq, hrange]
  set ΦN := (Φ.subgroupMap (Subgroup.normalizer (ρ.range : Set (Equiv.Perm Ω)))).trans
    (MulEquiv.subgroupCongr hnorm) with hΦN
  have hcoe : ∀ z, ((ΦN.symm z : Subgroup.normalizer (ρ.range : Set (Equiv.Perm Ω))) :
      Equiv.Perm Ω) = Φ.symm z := fun z => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (ΦN.apply_symm_apply z)
  refine ⟨QuotientGroup.congr _ _ ΦN ?_⟩
  ext y
  change y ∈ Subgroup.map ΦN.toMonoidHom _ ↔ _
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hcoe,
    ← Subgroup.mem_map_equiv, hrange]

end Transport

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def unitaryProjLineAction (h : UnitaryFieldData p f K) (n : ℕ) :
    unitaryPSU h n →* Equiv.Perm (isotropicLines h n) :=
  QuotientGroup.lift (unitaryScalars h n) (MulAction.toPermHom _ _) fun _ hg =>
    Equiv.ext fun L => Subtype.ext (smul_submodule_of_mem_normOneScalars hg L)

abbrev unitaryLineNormalizer (h : UnitaryFieldData p f K) (n : ℕ) :
    Subgroup (Equiv.Perm (isotropicLines h n)) :=
  Subgroup.normalizer ((unitaryProjLineAction h n).range : Set (Equiv.Perm (isotropicLines h n)))

theorem unitaryProjLineAction_injective (h : UnitaryFieldData p f K) {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (unitaryProjLineAction h n) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (unitaryScalars h n) x
  have hx' : MulAction.toPermHom (unitarySU p f K n) (isotropicLines h n) g = 1 := hx
  have hg : g ∈ unitaryScalars h n := by
    rw [← unitary_isotropic_kernel h hn]
    exact hx'
  exact (QuotientGroup.eq_one_iff g).mpr hg

theorem exists_transportLines (h : UnitaryFieldData p f K) {r ε : ℕ}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R) :
    ∃ j : hypIsotropicLines h r ε ≃ isotropicLines h (2 * r + ε), ∀ x : hypPSU h r ε,
      j.permCongr (hypProjLineAction h r ε x) =
        unitaryProjLineAction h (2 * r + ε) (hypProjTransport h hR x) := by
  set T := transportSubspace h hR
  let j : hypIsotropicLines h r ε ≃ isotropicLines h (2 * r + ε) :=
    { toFun := fun L => ⟨T L, (transportSubspace_mem_isotropicLines hR L).mpr L.2⟩
      invFun := fun L' => ⟨T.symm L', (transportSubspace_mem_isotropicLines hR _).mp
        (by rw [OrderIso.apply_symm_apply]; exact L'.2)⟩
      left_inv := fun L => Subtype.ext (T.symm_apply_apply L)
      right_inv := fun L' => Subtype.ext (T.apply_symm_apply L') }
  have hj : ∀ (g : hypSU h r ε) (L : hypIsotropicLines h r ε),
      j (g • L) = hypTransport h hR g • j L := fun g L =>
    Subtype.ext (transportSubspace_smul hR g L)
  refine ⟨j, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
  rw [hypProjTransport_hypProj]
  refine Equiv.ext fun L' => ?_
  obtain ⟨L, rfl⟩ := j.surjective L'
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact hj g L

theorem unitary_classical_model_outer_normalizer {H : Type} [Group H] {n p f : ℕ}
    (hH : StatedClassicalModel H .PSU n p f) :
    (∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K), Nonempty (H ≃* unitaryPSU h n)) ∧
    ∀ (K : Type) [Field K] (h : UnitaryFieldData p f K), (H ≃* unitaryPSU h n) →
      Function.Injective (unitaryProjLineAction h n) ∧
      Nonempty (Outer H ≃* unitaryLineNormalizer h n ⧸
        (unitaryProjLineAction h n).range.subgroupOf (unitaryLineNormalizer h n)) ∧
      (Group.IsSolvable (Outer H) ↔ Group.IsSolvable (unitaryLineNormalizer h n ⧸
        (unitaryProjLineAction h n).range.subgroupOf (unitaryLineNormalizer h n))) := by
  obtain ⟨⟨hp, hf, hn3, -⟩, K₀, _, _, hcard, ⟨e₀⟩⟩ := hH
  refine ⟨⟨K₀, inferInstance, ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩,
    ⟨e₀.trans (unitaryPSUEquiv _ (by omega)).symm⟩⟩, fun K _ h e => ?_⟩
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  have hr : 1 ≤ r := by omega
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  obtain ⟨j, hj⟩ := exists_transportLines h hR
  obtain ⟨E⟩ := nonempty_normalizerQuotient_mulEquiv j (hypProjTransport h hR) hj
  have hO₁ := outer_isomorphism e
  have hO₂ := outer_isomorphism (hypProjTransport h hR).symm
  obtain ⟨⟨e₁, -⟩, -⟩ := hO₁
  obtain ⟨⟨e₂, -⟩, -⟩ := hO₂
  have F := ((e₁.trans e₂).trans (linePermOuterEquiv h hr hε)).trans E
  exact ⟨unitaryProjLineAction_injective h (by omega), ⟨F⟩,
    ⟨fun _ => Group.isSolvable_of_surjective (f := F.toMonoidHom) F.surjective,
      fun _ => Group.isSolvable_of_surjective (f := F.symm.toMonoidHom) F.symm.surjective⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
