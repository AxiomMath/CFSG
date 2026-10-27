module

public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteSummandExchange
public import CFSG.CharacterTheory.TwoRankLowerBound.CoordinateTrace

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def scalarActionEndomorphism (ring : Type*) [CommRing ring]
    {algebra vector : Type*} [Ring algebra] [Algebra ring algebra]
    [AddCommGroup vector] [Module ring vector] [Module algebra vector]
    [IsScalarTower ring algebra vector] (scalar : algebra) : Module.End ring vector :=
  { toFun := fun value => scalar • value
    map_add' := smul_add scalar
    map_smul' := by
      intro coefficient value
      exact smul_comm scalar coefficient value }

theorem scalarActionEndomorphism_apply (ring : Type*) [CommRing ring]
    {algebra vector : Type*} [Ring algebra] [Algebra ring algebra]
    [AddCommGroup vector] [Module ring vector] [Module algebra vector]
    [IsScalarTower ring algebra vector] (scalar : algebra) (value : vector) :
    scalarActionEndomorphism ring scalar value = scalar • value := rfl

theorem scalarActionEndomorphism_conjugate {ring algebra vector target : Type*}
    [CommRing ring] [Ring algebra] [Algebra ring algebra]
    [AddCommGroup vector] [Module ring vector] [Module algebra vector]
    [IsScalarTower ring algebra vector] [AddCommGroup target] [Module ring target]
    [Module algebra target] [IsScalarTower ring algebra target]
    (equivalence : vector ≃ₗ[algebra] target) (scalar : algebra) :
    (equivalence.restrictScalars ring).conj (scalarActionEndomorphism ring scalar) =
      scalarActionEndomorphism ring scalar := by
  apply LinearMap.ext
  intro value
  change equivalence (scalar • equivalence.symm value) = scalar • value
  rw [equivalence.map_smul, equivalence.apply_symm_apply]

theorem scalarActionEndomorphism_trace_equiv {ring algebra vector target : Type*}
    [CommRing ring] [Ring algebra] [Algebra ring algebra]
    [AddCommGroup vector] [Module ring vector] [Module algebra vector]
    [IsScalarTower ring algebra vector] [AddCommGroup target] [Module ring target]
    [Module algebra target] [IsScalarTower ring algebra target]
    (equivalence : vector ≃ₗ[algebra] target) (scalar : algebra) :
    LinearMap.trace ring vector (scalarActionEndomorphism ring scalar) =
      LinearMap.trace ring target (scalarActionEndomorphism ring scalar) := by
  rw [← LinearMap.trace_conj' _ (equivalence.restrictScalars ring),
    scalarActionEndomorphism_conjugate]

theorem idempotent_scalarAction_trace_range {ring algebra vector : Type*}
    [CommRing ring] [Ring algebra] [Algebra ring algebra] [AddCommGroup vector]
    [Module ring vector] [Module algebra vector] [IsScalarTower ring algebra vector]
    [Module.Free ring vector] [Module.Finite ring vector]
    (projection : Module.End algebra vector) (hidempotent : IsIdempotentElem projection)
    [Module.Free ring projection.range] [Module.Finite ring projection.range] (scalar : algebra) :
    LinearMap.trace ring vector ((projection.restrictScalars ring).comp
      (scalarActionEndomorphism ring scalar)) =
      LinearMap.trace ring projection.range (scalarActionEndomorphism ring scalar) := by
  let inclusion : projection.range →ₗ[ring] vector := projection.range.subtype.restrictScalars ring
  let retraction : vector →ₗ[ring] projection.range := projection.rangeRestrict.restrictScalars ring
  have hexpansion : (projection.restrictScalars ring).comp (scalarActionEndomorphism ring scalar) =
      inclusion.comp (retraction.comp (scalarActionEndomorphism ring scalar)) := by
    apply LinearMap.ext
    intro value
    rfl
  rw [hexpansion, LinearMap.trace_comp_comm']
  congr 1
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  change projection (scalar • value.val) = scalar • value.val
  rw [projection.map_smul, LinearMap.IsIdempotentElem.mem_range_iff hidempotent |>.mp value.property]

theorem finite_local_summand_scalar_trace_zero {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (size : ℕ) (vector : Fin size → Type*)
    [∀ label, AddCommGroup (vector label)] [∀ label, Module ring (vector label)]
    [∀ label, Module algebra (vector label)] [∀ label, IsScalarTower ring algebra (vector label)]
    [∀ label, Module.Free ring (vector label)] [∀ label, Module.Finite ring (vector label)]
    (hlocal : ∀ label, ∀ operator : Module.End algebra (vector label),
      IsUnit operator ∨ IsUnit (1 - operator))
    (scalar : algebra)
    (hzero : ∀ label, LinearMap.trace ring (vector label) (scalarActionEndomorphism ring scalar) = 0)
    (projection : Module.End algebra (∀ label, vector label))
    (hidempotent : IsIdempotentElem projection) :
    LinearMap.trace ring (∀ label, vector label) ((projection.restrictScalars ring).comp
      (scalarActionEndomorphism ring scalar)) = 0 := by
  obtain ⟨support, ⟨rangeEquivalence⟩⟩ := finite_local_endomorphism_summand_exchange algebra
    size vector hlocal projection hidempotent
  let equivalence := rangeEquivalence.trans (supportedCoordinatesEquiv (ring := algebra) vector support)
  let := Module.Free.of_equiv (equivalence.restrictScalars ring).symm
  let := Module.Finite.equiv (equivalence.restrictScalars ring).symm
  rw [idempotent_scalarAction_trace_range projection hidempotent,
    scalarActionEndomorphism_trace_equiv equivalence]
  have hcoordinate : scalarActionEndomorphism ring scalar =
      coordinatewiseEndomorphism (fun label : support => vector label.val)
        (fun _ => scalarActionEndomorphism ring scalar) := by
    apply LinearMap.ext
    intro value
    rfl
  rw [hcoordinate, coordinatewiseEndomorphism_trace]
  exact Finset.sum_eq_zero (fun label _ => hzero label.val)

end CFSG.TwoRankLowerBound.Helpers
