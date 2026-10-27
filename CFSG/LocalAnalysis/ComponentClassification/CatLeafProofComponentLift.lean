module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_component_lift {C F₀ : Type*} [Group C] [Group F₀] (π : C →* F₀)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center C) {L : Subgroup F₀}
    (hL : IsComponent L) :
    ∃ M : Subgroup C, IsComponent M ∧ Nonempty (M ⧸ center M ≃* L ⧸ center L) := by
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
  obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hHq _ hsurj
    hker'
  let eM := (commutator H).equivMapOfInjective H.subtype H.subtype_injective
  refine ⟨(commutator H).map H.subtype, ⟨LocalCores.isQuasisimple_of_mulEquiv eM hHq, ?_⟩,
    ⟨(QuotientGroup.congr _ _ eM.symm (Subgroup.map_center_eq eM.symm)).trans e⟩⟩
  refine Subgroup.IsSubnormal.step _ H (Subgroup.map_subtype_le _) (hL.2.comap π) ?_
  rw [show ((commutator H).map H.subtype).subgroupOf H = commutator H from
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
  infer_instance

theorem isComponent_map_subtype_of_normal {C : Type*} [Group C] {N : Subgroup C} [N.Normal]
    {M : Subgroup N} (hM : IsComponent M) : IsComponent (M.map N.subtype) := by
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv
    (M.equivMapOfInjective N.subtype N.subtype_injective) hM.1, ?_⟩
  refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le M) ?_
    (Subgroup.Normal.isSubnormal inferInstance)
  rw [show (M.map N.subtype).subgroupOf N = M from
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective M]
  exact hM.2

theorem exists_component_of_quotientFixed {X : Type*} [Group X] (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ center X) (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z)
    {L : Subgroup (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv))}
    (hL : IsComponent L) :
    ∃ M : Subgroup (fixedSubgroup ψ), IsComponent M ∧
      Nonempty (L ⧸ center L ≃* M ⧸ center M) := by
  set F₀ := CatalogueBFixedCentralQuotient.fixedImage Z ψ hinv
  have hLF₀ : L ≤ F₀ := by
    calc L = ⁅L, L⁆ := (Subgroup.isPerfect_iff.mp hL.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
      _ ≤ F₀ := CatalogueBFixedCentralQuotient.fixed_commutator_le_image Z ψ hinv hcentral
  let eL := Subgroup.subgroupOfEquivOfLe hLF₀
  have hL' : IsComponent (L.subgroupOf F₀) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv eL.symm hL.1, hL.2.subgroupOf⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_component_lift
    (CatalogueBFixedCentralQuotient.fixedImageProjection Z ψ hinv)
    (CatalogueBFixedCentralQuotient.fixedImageProjection_surjective Z ψ hinv)
    (CatalogueBFixedCentralQuotient.fixedImageProjection_kernel_central Z ψ hinv hcentral) hL'
  exact ⟨M, hM, ⟨(QuotientGroup.congr _ _ eL.symm (Subgroup.map_center_eq eL.symm)).trans
    e.symm⟩⟩

open CatalogueBOrthogonalLinearFixed in
theorem exists_component_of_normalQuotientFixed {X : Type*} [Group X] (N Z : Subgroup X)
    [N.Normal] [Z.Normal] (hcentral : Z ≤ center X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)
    {L : Subgroup (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ))} (hL : IsComponent L) :
    ∃ M : Subgroup (fixedSubgroup ψ), IsComponent M ∧
      Nonempty (L ⧸ center L ≃* M ⧸ center M) := by
  obtain ⟨M₁, hM₁, ⟨e₁⟩⟩ := exists_component_of_quotientFixed (Z.subgroupOf N)
    (central_subgroupOf N Z hcentral) (restrictAutomorphism N ψ hN)
    (restricted_central_invariant N Z ψ hN hZ) hL
  let Φ := fixedNormalEquiv N ψ hN
  have hM₂ := LocalCores.isComponent_map_mulEquiv Φ hM₁
  have : (N.subgroupOf (fixedSubgroup ψ)).Normal := Subgroup.Normal.subgroupOf inferInstance _
  let e₂ := M₁.equivMapOfInjective Φ.toMonoidHom Φ.injective
  let e₃ := (M₁.map Φ.toMonoidHom).equivMapOfInjective (N.subgroupOf (fixedSubgroup ψ)).subtype
    (N.subgroupOf (fixedSubgroup ψ)).subtype_injective
  exact ⟨_, isComponent_map_subtype_of_normal hM₂, ⟨e₁.trans
    ((QuotientGroup.congr _ _ (e₂.trans e₃) (Subgroup.map_center_eq _)))⟩⟩

theorem oddLieCentralQuotient_of_centerQuotient_equiv {p : ℕ} {L M : Type} [Group L] [Group M]
    (e : L ⧸ center L ≃* M ⧸ center M) (h : OddLieCentralQuotient p M) :
    OddLieCentralQuotient p L := by
  obtain ⟨τ', n', f', hadm, hM⟩ := h
  exact ⟨τ', n', f', hadm, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hM⟩

end CFSG.ComponentClassification.CatLeafProof
