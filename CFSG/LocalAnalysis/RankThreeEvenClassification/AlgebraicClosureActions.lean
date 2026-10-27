module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableQuadraticPairs

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

noncomputable def algebraicClosureLinearAction (field : Type u) (space : Type v)
    [Field field] [AddCommGroup space] [Module field space] :
    (space ≃ₗ[field] space) →*
      (TensorProduct field (AlgebraicClosure field) space ≃ₗ[AlgebraicClosure field]
        TensorProduct field (AlgebraicClosure field) space) where
  toFun := LinearEquiv.baseChange field (AlgebraicClosure field) space space
  map_one' := LinearEquiv.baseChange_one field (AlgebraicClosure field) space
  map_mul' := LinearEquiv.baseChange_mul field (AlgebraicClosure field) space

theorem algebraicClosureLinearAction_injective (field : Type u) (space : Type v)
    [Field field] [AddCommGroup space] [Module field space] :
    Function.Injective (algebraicClosureLinearAction field space) := by
  intro first second heq
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.baseChangeHom_injective field space (AlgebraicClosure field)
  exact congrArg (fun equivalence => equivalence.toLinearMap) heq

theorem quadratic_algebraicClosureLinearAction {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (equivalence : space ≃ₗ[field] space)
    (hquadratic : ((equivalence : Module.End field space) - LinearMap.id) ^ 2 = 0) :
    ((algebraicClosureLinearAction field space equivalence :
      Module.End (AlgebraicClosure field) (TensorProduct field (AlgebraicClosure field) space)) - LinearMap.id) ^ 2 = 0 := by
  have heq := congrArg (LinearMap.baseChange (AlgebraicClosure field)) hquadratic
  rw [LinearMap.baseChange_pow, LinearMap.baseChange_sub, LinearMap.baseChange_id,
    LinearMap.baseChange_zero] at heq
  exact heq

theorem solvable_quadratic_pair_isPGroup {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [FiniteDimensional field space]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) [CharP field prime]
    (first second : space ≃ₗ[field] space)
    (hfirst : ((first : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (hsecond : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0)
    [Finite (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))]
    [Group.IsSolvable (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))]
    (halternative : 5 ≤ prime ∨
      Odd (Nat.card (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space)))) :
    IsPGroup prime (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space)) := by
  let action := algebraicClosureLinearAction field space
  let pair := Subgroup.zpowers first ⊔ Subgroup.zpowers second
  let imagePair := Subgroup.zpowers (action first) ⊔ Subgroup.zpowers (action second)
  have hmap : pair.map action = imagePair := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  let equivalence := (pair.equivMapOfInjective action (algebraicClosureLinearAction_injective field space)).trans
    (MulEquiv.subgroupCongr hmap)
  have : Finite imagePair := Finite.of_surjective equivalence equivalence.surjective
  have : Group.IsSolvable imagePair := Group.isSolvable_of_surjective
    (f := equivalence.toMonoidHom) equivalence.surjective
  have himageAlternative : 5 ≤ prime ∨ Odd (Nat.card imagePair) := by
    rw [← Nat.card_congr equivalence.toEquiv]
    exact halternative
  exact (solvable_quadratic_pair_isPGroup_algebraically_closed prime hprime hodd (action first) (action second)
    (quadratic_algebraicClosureLinearAction first hfirst)
    (quadratic_algebraicClosureLinearAction second hsecond) himageAlternative).of_equiv equivalence.symm

end CFSG.RankThreeEvenClassification.Helpers
