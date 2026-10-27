module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_component_cover {C F₀ : Type*} [Group C] [Group F₀] (π : C →* F₀)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center C) {L : Subgroup F₀}
    (hL : IsComponent L) :
    ∃ M : Subgroup C, IsComponent M ∧
      ∃ σ : M →* L, Function.Surjective σ ∧ σ.ker ≤ center M := by
  set H := L.comap π
  let f : H →* L := (π.comp H.subtype).codRestrict L fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hkerf : f.ker ≤ center H := by
    intro x hx
    have hx1 : π x.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hx1)) y.val)
  have hHq := LocalCores.quasisimple_central_extension_derived_of_surjective f hf hkerf hL.1
  obtain ⟨-, -, hsurj⟩ := LocalCores.central_extension_derived_of_surjective f hf hkerf hL.1.1
  have hker' : (f.comp (commutator H).subtype).ker ≤ center (commutator H) := by
    intro x hx
    have hxc := hkerf (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc y.val)
  let eM := (commutator H).equivMapOfInjective H.subtype H.subtype_injective
  refine ⟨(commutator H).map H.subtype, ⟨LocalCores.isQuasisimple_of_mulEquiv eM hHq, ?_⟩,
    (f.comp (commutator H).subtype).comp eM.symm.toMonoidHom,
    hsurj.comp eM.symm.surjective, fun x hx => ?_⟩
  · refine Subgroup.IsSubnormal.step _ H (Subgroup.map_subtype_le _) (hL.2.comap π) ?_
    rw [show ((commutator H).map H.subtype).subgroupOf H = commutator H from
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
    infer_instance
  · have h1 : eM.symm x ∈ center (commutator H) :=
      hker' (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro y
    apply eM.symm.injective
    rw [map_mul, map_mul, h1]

theorem isPGroup_center_of_cover {M L : Type*} [Group M] [Group L] (hM : Group.IsPerfect M)
    (σ : M →* L) (hσ : Function.Surjective σ) (hker : σ.ker ≤ center M)
    (h : IsPGroup 2 (center M)) : IsPGroup 2 (center L) := by
  have hc := LocalCores.comap_center_eq_of_perfect hM σ hσ hker
  intro z
  obtain ⟨m, hm⟩ := hσ z
  have hmc : m ∈ center M := by
    rw [← hc, Subgroup.mem_comap, hm]
    exact z.2
  obtain ⟨n, hn⟩ := h ⟨m, hmc⟩
  have hn' : m ^ 2 ^ n = 1 := congrArg Subtype.val hn
  refine ⟨n, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, ← hm, ← map_pow, hn', map_one]
  rfl

theorem exists_component_cover_of_quotientFixed {X : Type*} [Group X] (Z : Subgroup X)
    [Z.Normal] (hcentral : Z ≤ center X) (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z)
    {L : Subgroup (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv))}
    (hL : IsComponent L) :
    ∃ M : Subgroup (fixedSubgroup ψ), IsComponent M ∧
      ∃ σ : M →* L, Function.Surjective σ ∧ σ.ker ≤ center M := by
  set F₀ := CatalogueBFixedCentralQuotient.fixedImage Z ψ hinv
  have hLF₀ : L ≤ F₀ := by
    calc L = ⁅L, L⁆ := (Subgroup.isPerfect_iff.mp hL.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
      _ ≤ F₀ := CatalogueBFixedCentralQuotient.fixed_commutator_le_image Z ψ hinv hcentral
  let eL := Subgroup.subgroupOfEquivOfLe hLF₀
  have hL' : IsComponent (L.subgroupOf F₀) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv eL.symm hL.1, hL.2.subgroupOf⟩
  obtain ⟨M, hM, σ, hσ, hker⟩ := exists_component_cover
    (CatalogueBFixedCentralQuotient.fixedImageProjection Z ψ hinv)
    (CatalogueBFixedCentralQuotient.fixedImageProjection_surjective Z ψ hinv)
    (CatalogueBFixedCentralQuotient.fixedImageProjection_kernel_central Z ψ hinv hcentral) hL'
  refine ⟨M, hM, eL.toMonoidHom.comp σ, eL.surjective.comp hσ, fun x hx => hker ?_⟩
  have hx' : eL (σ x) = 1 := MonoidHom.mem_ker.mp hx
  exact MonoidHom.mem_ker.mpr (eL.injective (hx'.trans (map_one eL).symm))

open CatalogueBOrthogonalLinearFixed in
theorem exists_component_cover_of_normalQuotientFixed {X : Type*} [Group X] (N Z : Subgroup X)
    [N.Normal] [Z.Normal] (hcentral : Z ≤ center X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)
    {L : Subgroup (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ))} (hL : IsComponent L) :
    ∃ M : Subgroup (fixedSubgroup ψ), IsComponent M ∧
      ∃ σ : M →* L, Function.Surjective σ ∧ σ.ker ≤ center M := by
  obtain ⟨M₁, hM₁, σ₁, hσ₁, hker₁⟩ : ∃ M : Subgroup (fixedSubgroup (restrictAutomorphism N ψ hN)),
      IsComponent M ∧ ∃ σ : M →* L, Function.Surjective σ ∧ σ.ker ≤ center M :=
    exists_component_cover_of_quotientFixed (Z.subgroupOf N) (central_subgroupOf N Z hcentral)
      (restrictAutomorphism N ψ hN) (restricted_central_invariant N Z ψ hN hZ) hL
  let Φ := fixedNormalEquiv N ψ hN
  have hM₂ := LocalCores.isComponent_map_mulEquiv Φ hM₁
  have : (N.subgroupOf (fixedSubgroup ψ)).Normal := Subgroup.Normal.subgroupOf inferInstance _
  let e₂ := M₁.equivMapOfInjective Φ.toMonoidHom Φ.injective
  let e₃ := (M₁.map Φ.toMonoidHom).equivMapOfInjective (N.subgroupOf (fixedSubgroup ψ)).subtype
    (N.subgroupOf (fixedSubgroup ψ)).subtype_injective
  let e := e₂.trans e₃
  refine ⟨_, isComponent_map_subtype_of_normal hM₂, σ₁.comp e.symm.toMonoidHom,
    hσ₁.comp e.symm.surjective, fun x hx => ?_⟩
  have h1 : e.symm x ∈ center M₁ := hker₁ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro y
  apply e.symm.injective
  rw [map_mul, map_mul, h1]

end CFSG.ComponentClassification.CatLeafProof
