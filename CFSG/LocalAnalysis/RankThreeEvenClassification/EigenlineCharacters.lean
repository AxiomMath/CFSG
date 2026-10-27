module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ProjectiveLinearActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

theorem invariant_eigenline_has_character {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (action : actor →* (space ≃ₗ[field] space)) (vector : space) (hne : vector ≠ 0)
    (hscalar : ∀ member : actor, ∃ scalar : field, action member vector = scalar • vector) :
    ∃ character : actor →* fieldˣ,
      ∀ member : actor, action member vector = (character member : field) • vector := by
  classical
  choose coefficient hcoefficient using hscalar
  have hcoefficientNe : ∀ member : actor, coefficient member ≠ 0 := by
    intro member hzero
    have heq := hcoefficient member
    rw [hzero, zero_smul] at heq
    exact hne ((action member).injective (heq.trans (map_zero (action member)).symm))
  let character : actor →* fieldˣ :=
    { toFun := fun member => Units.mk0 (coefficient member) (hcoefficientNe member)
      map_one' := by
        apply Units.ext
        change coefficient 1 = 1
        apply smul_left_injective field hne
        change coefficient 1 • vector = (1 : field) • vector
        rw [← hcoefficient, map_one, one_smul]
        rfl
      map_mul' := by
        intro first second
        apply Units.ext
        change coefficient (first * second) = coefficient first * coefficient second
        apply smul_left_injective field hne
        change coefficient (first * second) • vector =
          (coefficient first * coefficient second) • vector
        rw [← hcoefficient, map_mul, LinearEquiv.mul_apply, hcoefficient second,
          map_smul, hcoefficient first, smul_smul]
        congr 1
        exact mul_comm _ _ }
  exact ⟨character, hcoefficient⟩

theorem distinct_projective_representatives_independent {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (first second : Projectivization field space) (hne : first ≠ second) :
    LinearIndependent field ![first.rep, second.rep] := by
  apply (LinearIndependent.pair_iff' first.rep_nonzero).mpr
  intro scalar heq
  apply hne
  have hprojective : Projectivization.mk field second.rep second.rep_nonzero =
      Projectivization.mk field first.rep first.rep_nonzero :=
    (Projectivization.mk_eq_mk_iff' field _ _ _ _).mpr ⟨scalar, heq⟩
  simpa only [Projectivization.mk_rep] using hprojective.symm

theorem distinct_projective_plane_representatives_span {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [FiniteDimensional field space]
    (hdimension : Module.finrank field space = 2)
    (first second : Projectivization field space) (hne : first ≠ second) :
    ∀ member : space, ∃ firstCoefficient secondCoefficient : field,
      firstCoefficient • first.rep + secondCoefficient • second.rep = member := by
  have hspan := (distinct_projective_representatives_independent first second hne).span_eq_top_of_card_eq_finrank
    (by simpa only [Fintype.card_fin] using hdimension.symm)
  rw [Matrix.range_cons_cons_empty] at hspan
  intro member
  apply Submodule.mem_span_pair.mp
  rw [hspan]
  trivial

theorem projective_identity_eigenbasis_scalars_eq {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (equivalence : space ≃ₗ[field] space)
    (hidentity : linearProjectiveAction field space equivalence = 1)
    (first second : space) (firstScalar secondScalar : field)
    (hfirstEigen : equivalence first = firstScalar • first)
    (hsecondEigen : equivalence second = secondScalar • second)
    (hindependent : ∀ firstCoefficient secondCoefficient : field,
      firstCoefficient • first + secondCoefficient • second = 0 →
        firstCoefficient = 0 ∧ secondCoefficient = 0) : firstScalar = secondScalar := by
  have hsumNe : first + second ≠ 0 := by
    intro heq
    have hzero : (1 : field) • first + (1 : field) • second = 0 := by
      simpa only [one_smul] using heq
    exact one_ne_zero (hindependent 1 1 hzero).1
  have hfixed : linearProjectiveAction field space equivalence
      (Projectivization.mk field (first + second) hsumNe) =
        Projectivization.mk field (first + second) hsumNe := by
    rw [hidentity]
    rfl
  obtain ⟨scalar, hscalar⟩ :=
    (projective_fixed_point_iff_eigenvector equivalence (first + second) hsumNe).mp hfixed
  rw [map_add, hfirstEigen, hsecondEigen, smul_add] at hscalar
  have hzero : (firstScalar - scalar) • first + (secondScalar - scalar) • second = 0 := by
    rw [sub_smul, sub_smul]
    calc
      _ = (firstScalar • first + secondScalar • second) -
          (scalar • first + scalar • second) := by abel
      _ = 0 := sub_eq_zero.mpr hscalar
  obtain ⟨hfirst, hsecond⟩ := hindependent _ _ hzero
  exact (sub_eq_zero.mp hfirst).trans (sub_eq_zero.mp hsecond).symm

end CFSG.RankThreeEvenClassification.Helpers
