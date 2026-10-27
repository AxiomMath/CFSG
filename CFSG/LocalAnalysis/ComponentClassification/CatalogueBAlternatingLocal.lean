module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingFixedSupport

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

open scoped Classical

theorem fixedPoints_ofSubtype_centralizes {Ω : Type*} (P : Subgroup (Equiv.Perm Ω))
    (f : Equiv.Perm (MulAction.fixedPoints P Ω)) :
    @Equiv.Perm.ofSubtype Ω (· ∈ MulAction.fixedPoints P Ω) (Classical.decPred _) f ∈
      Subgroup.centralizer (P : Set (Equiv.Perm Ω)) := by
  classical
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  apply Equiv.ext
  intro x
  change g (Equiv.Perm.ofSubtype f x) = Equiv.Perm.ofSubtype f (g x)
  by_cases hx : x ∈ MulAction.fixedPoints P Ω
  · have hgx : g x = x := MulAction.mem_fixedPoints.mp hx (⟨g, hg⟩ : P)
    rw [hgx, Equiv.Perm.ofSubtype_apply_of_mem _ hx]
    exact MulAction.mem_fixedPoints.mp (f ⟨x, hx⟩).property (⟨g, hg⟩ : P)
  · have hgx : g x ∉ MulAction.fixedPoints P Ω := by
      intro h
      have hfix := MulAction.mem_fixedPoints.mp h (⟨g⁻¹, P.inv_mem hg⟩ : P)
      change g.symm (g x) = g x at hfix
      rw [Equiv.symm_apply_apply] at hfix
      exact hx (hfix.symm ▸ h)
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx,
      Equiv.Perm.ofSubtype_apply_of_not_mem _ hgx]

@[expose] noncomputable def fixedPointsNormalizerHom {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) :
    Equiv.Perm (MulAction.fixedPoints P Ω) →*
      Subgroup.normalizer (P : Set (Equiv.Perm Ω)) := by
  classical
  exact
    { toFun f := ⟨Equiv.Perm.ofSubtype f,
        Subgroup.centralizer_le_normalizer _ (fixedPoints_ofSubtype_centralizes P f)⟩
      map_one' := Subtype.ext (map_one Equiv.Perm.ofSubtype)
      map_mul' f g := Subtype.ext (map_mul Equiv.Perm.ofSubtype f g) }

theorem fixedPointsNormalizerHom_coe {Ω : Type*} (P : Subgroup (Equiv.Perm Ω))
    (f : Equiv.Perm (MulAction.fixedPoints P Ω)) :
    (fixedPointsNormalizerHom P f).val =
      @Equiv.Perm.ofSubtype Ω (· ∈ MulAction.fixedPoints P Ω) (Classical.decPred _) f := rfl

theorem fixedPointsNormalizerHom_injective {Ω : Type*} (P : Subgroup (Equiv.Perm Ω)) :
    Function.Injective (fixedPointsNormalizerHom P) := by
  classical
  intro f g h
  exact Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)

theorem normalizer_pComponent_le_fixedPoints_range {Ω : Type*} [Finite Ω]
    (p : ℕ) [Fact p.Prime] (P : Subgroup (Equiv.Perm Ω)) (hP : IsPGroup p P)
    (L : Subgroup (Subgroup.normalizer (P : Set (Equiv.Perm Ω))))
    (hL : CFSG.IsPComponent p L) : L ≤ (fixedPointsNormalizerHom P).range := by
  classical
  intro c hc
  have hsupport := normalizer_pComponent_fixedSupport p P hP L hL ⟨c, hc⟩
  have hpreserves : ∀ x : Ω,
      c.val x ∈ MulAction.fixedPoints P Ω ↔ x ∈ MulAction.fixedPoints P Ω := by
    intro x
    constructor
    · intro h
      by_contra hx
      exact hx (hsupport x hx ▸ h)
    · intro hx
      by_contra h
      have hfix := hsupport (c.val x) h
      exact h ((c.val.injective hfix).symm ▸ hx)
  refine ⟨c.val.subtypePerm hpreserves, ?_⟩
  apply Subtype.ext
  exact Equiv.Perm.ofSubtype_subtypePerm hpreserves
    (fun x h => by_contra fun hx => h (hsupport x hx))

theorem symmetric_normalizer_pComponent {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : ℕ) [Fact p.Prime] (P : Subgroup (Equiv.Perm Ω)) (hP : IsPGroup p P)
    (L : Subgroup (Subgroup.normalizer (P : Set (Equiv.Perm Ω))))
    (hL : CFSG.IsPComponent p L) :
    5 ≤ Nat.card (MulAction.fixedPoints P Ω) ∧
      L = (alternatingGroup (MulAction.fixedPoints P Ω)).map (fixedPointsNormalizerHom P) ∧
      CFSG.IsQuasisimple L := by
  classical
  let f := fixedPointsNormalizerHom P
  let J := L.comap f
  have hmap : J.map f = L :=
    Subgroup.map_comap_eq_self (normalizer_pComponent_le_fixedPoints_range p P hP L hL)
  let e : J ≃* L := (J.equivMapOfInjective f (fixedPointsNormalizerHom_injective P)).trans
    (MulEquiv.subgroupCongr hmap)
  let : Group.IsPerfect L := pComponent_perfect hL
  let : Nontrivial L := pComponent_nontrivial hL
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : Nontrivial J := e.toEquiv.nontrivial
  have hsubnormal : J.IsSubnormal := hL.choose_spec.2.1.comap f
  obtain ⟨hdegree, hJ⟩ := symmetric_perfect_subnormal J hsubnormal
  refine ⟨hdegree, hmap.symm.trans (congrArg (Subgroup.map f) hJ), ?_⟩
  apply quasisimple_iff_native.mpr
  apply Components.quasisimple_of_equiv e.symm
  exact Components.quasisimple_of_equiv (MulEquiv.subgroupCongr hJ)
    (alternating_quasisimple hdegree)

theorem symmetric_normalizer_badSubgroup_eq_bot {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : Subgroup (Equiv.Perm Ω)) (hP : IsPGroup 2 P) :
    TwoComponents.badSubgroup (Subgroup.normalizer (P : Set (Equiv.Perm Ω))) = ⊥ := by
  apply le_bot_iff.mp
  apply sSup_le
  intro L hL
  exact (hL.2 (quasisimple_iff_native.mp
    (symmetric_normalizer_pComponent 2 P hP L ((pComponent_two_iff L).mpr hL.1)).2.2)).elim

end CFSG.ComponentClassification.CatalogueBAlternating
