module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantLinearActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

theorem quadratic_linear_subspace_action {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (action : actor →* (space ≃ₗ[field] space)) (subspace : Submodule field space)
    (hinvariant : ∀ member : actor, subspace.map (action member : Module.End field space) = subspace)
    (member : actor) (hquadratic : ((action member : Module.End field space) - LinearMap.id) ^ 2 = 0) :
    ((linearSubspaceAction action subspace hinvariant member : Module.End field subspace) - LinearMap.id) ^ 2 = 0 := by
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  have heq := DFunLike.congr_fun hquadratic (vector : space)
  rw [pow_two, Module.End.mul_apply] at heq ⊢
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply] at heq ⊢
  change action member (action member (vector : space) - (vector : space)) -
    (action member (vector : space) - (vector : space)) = 0
  exact heq

theorem quadratic_linear_quotient_action {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (action : actor →* (space ≃ₗ[field] space)) (subspace : Submodule field space)
    (hinvariant : ∀ member : actor, subspace.map (action member : Module.End field space) = subspace)
    (member : actor) (hquadratic : ((action member : Module.End field space) - LinearMap.id) ^ 2 = 0) :
    ((linearQuotientAction action subspace hinvariant member : Module.End field (space ⧸ subspace)) - LinearMap.id) ^ 2 = 0 := by
  apply LinearMap.ext
  intro vector
  obtain ⟨preimage, rfl⟩ := subspace.mkQ_surjective vector
  have heq := congrArg subspace.mkQ (DFunLike.congr_fun hquadratic preimage)
  rw [pow_two, Module.End.mul_apply] at heq ⊢
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply] at heq ⊢
  change linearQuotientAction action subspace hinvariant member
    (linearQuotientAction action subspace hinvariant member (subspace.mkQ preimage) - subspace.mkQ preimage) -
      (linearQuotientAction action subspace hinvariant member (subspace.mkQ preimage) - subspace.mkQ preimage) = 0
  rw [linearQuotientAction_apply, ← map_sub, linearQuotientAction_apply]
  change subspace.mkQ (action member (action member preimage - preimage) -
    (action member preimage - preimage)) = subspace.mkQ 0 at heq
  rw [map_sub, map_zero] at heq
  exact heq

end CFSG.RankThreeEvenClassification.Helpers
