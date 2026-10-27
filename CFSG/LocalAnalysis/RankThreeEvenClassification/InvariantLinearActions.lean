module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

theorem quotient_linear_equiv_apply_mk {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (subspace : Submodule field space) (equivalence : space ≃ₗ[field] space)
    (heq : subspace.map (equivalence : Module.End field space) = subspace) (member : space) :
    (Submodule.Quotient.equiv subspace subspace equivalence heq) (subspace.mkQ member) =
      subspace.mkQ (equivalence member) := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  rfl

@[expose] noncomputable def linearSubspaceAction {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (action : actor →* (space ≃ₗ[field] space)) (subspace : Submodule field space)
    (hinvariant : ∀ member : actor, subspace.map (action member : Module.End field space) = subspace) :
    actor →* (subspace ≃ₗ[field] subspace) where
  toFun member := (action member).ofSubmodules subspace subspace (hinvariant member)
  map_one' := by
    apply LinearEquiv.ext
    intro member
    apply Subtype.ext
    rw [LinearEquiv.ofSubmodules_apply, map_one]
    rfl
  map_mul' first second := by
    apply LinearEquiv.ext
    intro member
    apply Subtype.ext
    rw [LinearEquiv.mul_apply, LinearEquiv.ofSubmodules_apply, LinearEquiv.ofSubmodules_apply,
      LinearEquiv.ofSubmodules_apply, map_mul, LinearEquiv.mul_apply]

theorem linearSubspaceAction_apply {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (action : actor →* (space ≃ₗ[field] space)) (subspace : Submodule field space)
    (hinvariant : ∀ member : actor, subspace.map (action member : Module.End field space) = subspace)
    (member : actor) (element : subspace) :
    ((linearSubspaceAction action subspace hinvariant member element : subspace) : space) =
      action member element :=
  LinearEquiv.ofSubmodules_apply (action member) (hinvariant member) element

@[expose] noncomputable def linearQuotientAction {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (action : actor →* (space ≃ₗ[field] space)) (subspace : Submodule field space)
    (hinvariant : ∀ member : actor, subspace.map (action member : Module.End field space) = subspace) :
    actor →* ((space ⧸ subspace) ≃ₗ[field] (space ⧸ subspace)) where
  toFun member := Submodule.Quotient.equiv subspace subspace (action member) (hinvariant member)
  map_one' := by
    apply LinearEquiv.ext
    intro member
    obtain ⟨member, rfl⟩ := subspace.mkQ_surjective member
    rw [quotient_linear_equiv_apply_mk, map_one]
    rfl
  map_mul' first second := by
    apply LinearEquiv.ext
    intro member
    obtain ⟨member, rfl⟩ := subspace.mkQ_surjective member
    rw [LinearEquiv.mul_apply, quotient_linear_equiv_apply_mk,
      quotient_linear_equiv_apply_mk, quotient_linear_equiv_apply_mk, map_mul, LinearEquiv.mul_apply]

theorem linearQuotientAction_apply {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (action : actor →* (space ≃ₗ[field] space)) (subspace : Submodule field space)
    (hinvariant : ∀ member : actor, subspace.map (action member : Module.End field space) = subspace)
    (member : actor) (element : space) :
    linearQuotientAction action subspace hinvariant member (subspace.mkQ element) =
      subspace.mkQ (action member element) :=
  quotient_linear_equiv_apply_mk subspace (action member) (hinvariant member) element

end CFSG.RankThreeEvenClassification.Helpers
