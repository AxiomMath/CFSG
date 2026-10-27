module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ProjectiveLinearActions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeSemisimpleActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem scalar_linear_projectiveAction_eq_one {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (equivalence : space ≃ₗ[field] space) (scalar : field)
    (hscalar : ∀ member : space, equivalence member = scalar • member) :
    linearProjectiveAction field space equivalence = 1 := by
  apply Equiv.ext
  intro point
  change linearProjectiveAction field space equivalence point = point
  rw [← Projectivization.mk_rep point]
  exact (projective_fixed_point_iff_eigenvector equivalence point.rep point.rep_nonzero).mpr
    ⟨scalar, hscalar point.rep⟩

theorem eigenbasis_distinct_scalars_fixed_points {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (equivalence : space ≃ₗ[field] space) (first second : space)
    (hfirstNe : first ≠ 0) (hsecondNe : second ≠ 0)
    (firstScalar secondScalar : field) (hscalarNe : firstScalar ≠ secondScalar)
    (hfirstEigen : equivalence first = firstScalar • first)
    (hsecondEigen : equivalence second = secondScalar • second)
    (hindependent : ∀ firstCoefficient secondCoefficient : field,
      firstCoefficient • first + secondCoefficient • second = 0 →
        firstCoefficient = 0 ∧ secondCoefficient = 0)
    (hspan : ∀ member : space, ∃ firstCoefficient secondCoefficient : field,
      firstCoefficient • first + secondCoefficient • second = member)
    (point : Projectivization field space) :
    linearProjectiveAction field space equivalence point = point ↔
      point = Projectivization.mk field first hfirstNe ∨
        point = Projectivization.mk field second hsecondNe := by
  constructor
  · intro hfixed
    have hrepFixed : linearProjectiveAction field space equivalence
        (Projectivization.mk field point.rep point.rep_nonzero) =
          Projectivization.mk field point.rep point.rep_nonzero := by
      simpa only [Projectivization.mk_rep] using hfixed
    obtain ⟨eigenvalue, heigenvalue⟩ :=
      (projective_fixed_point_iff_eigenvector equivalence point.rep point.rep_nonzero).mp hrepFixed
    obtain ⟨firstCoefficient, secondCoefficient, hcoefficients⟩ := hspan point.rep
    have heq : (firstCoefficient * firstScalar) • first +
        (secondCoefficient * secondScalar) • second =
          (eigenvalue * firstCoefficient) • first +
            (eigenvalue * secondCoefficient) • second := by
      rw [← hcoefficients, map_add, map_smul, map_smul, hfirstEigen, hsecondEigen,
        smul_add, smul_smul, smul_smul, smul_smul, smul_smul] at heigenvalue
      exact heigenvalue
    have hzero : (firstCoefficient * firstScalar - eigenvalue * firstCoefficient) • first +
        (secondCoefficient * secondScalar - eigenvalue * secondCoefficient) • second = 0 := by
      rw [sub_smul, sub_smul]
      calc
        _ = ((firstCoefficient * firstScalar) • first +
          (secondCoefficient * secondScalar) • second) -
            ((eigenvalue * firstCoefficient) • first +
              (eigenvalue * secondCoefficient) • second) := by abel
        _ = 0 := sub_eq_zero.mpr heq
    obtain ⟨hfirstZero, hsecondZero⟩ := hindependent _ _ hzero
    have hfirstProduct : firstCoefficient * (firstScalar - eigenvalue) = 0 := by
      calc
        _ = firstCoefficient * firstScalar - eigenvalue * firstCoefficient := by ring
        _ = 0 := hfirstZero
    have hsecondProduct : secondCoefficient * (secondScalar - eigenvalue) = 0 := by
      calc
        _ = secondCoefficient * secondScalar - eigenvalue * secondCoefficient := by ring
        _ = 0 := hsecondZero
    have hcoefficientZero : firstCoefficient = 0 ∨ secondCoefficient = 0 := by
      by_cases hfirstCoefficient : firstCoefficient = 0
      · exact Or.inl hfirstCoefficient
      · right
        have hfirstValue := sub_eq_zero.mp ((mul_eq_zero.mp hfirstProduct).resolve_left hfirstCoefficient)
        have hsecondValueNe : secondScalar - eigenvalue ≠ 0 := by
          intro heqZero
          exact hscalarNe (hfirstValue.trans (sub_eq_zero.mp heqZero).symm)
        exact (mul_eq_zero.mp hsecondProduct).resolve_right hsecondValueNe
    rcases hcoefficientZero with hfirstCoefficient | hsecondCoefficient
    · right
      rw [hfirstCoefficient, zero_smul, zero_add] at hcoefficients
      have heqProjective : Projectivization.mk field point.rep point.rep_nonzero =
          Projectivization.mk field second hsecondNe :=
        (Projectivization.mk_eq_mk_iff' field _ _ _ _).mpr ⟨secondCoefficient, hcoefficients⟩
      simpa only [Projectivization.mk_rep] using heqProjective
    · left
      rw [hsecondCoefficient, zero_smul, add_zero] at hcoefficients
      have heqProjective : Projectivization.mk field point.rep point.rep_nonzero =
          Projectivization.mk field first hfirstNe :=
        (Projectivization.mk_eq_mk_iff' field _ _ _ _).mpr ⟨firstCoefficient, hcoefficients⟩
      simpa only [Projectivization.mk_rep] using heqProjective
  · rintro (rfl | rfl)
    · exact (projective_fixed_point_iff_eigenvector equivalence first hfirstNe).mpr
        ⟨firstScalar, hfirstEigen⟩
    · exact (projective_fixed_point_iff_eigenvector equivalence second hsecondNe).mpr
        ⟨secondScalar, hsecondEigen⟩

theorem semisimple_plane_nonidentity_projective_has_fixed_pair {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (equivalence : space ≃ₗ[field] space)
    (hsemisimple : Module.End.IsSemisimple (equivalence : Module.End field space))
    (hne : linearProjectiveAction field space equivalence ≠ 1) :
    ∃ first second : Projectivization field space, first ≠ second ∧
      ∀ point : Projectivization field space,
        linearProjectiveAction field space equivalence point = point ↔
          point = first ∨ point = second := by
  obtain ⟨first, second, hfirstNe, hsecondNe, firstScalar, secondScalar,
    hfirstEigen, hsecondEigen, hindependent, hspan⟩ :=
    semisimple_plane_has_eigenbasis hdimension equivalence hsemisimple
  have hscalarNe : firstScalar ≠ secondScalar := by
    intro heq
    apply hne
    apply scalar_linear_projectiveAction_eq_one equivalence firstScalar
    intro member
    obtain ⟨firstCoefficient, secondCoefficient, rfl⟩ := hspan member
    rw [map_add, map_smul, map_smul, hfirstEigen, hsecondEigen, ← heq,
      smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring
  have hpointsNe : Projectivization.mk field first hfirstNe ≠
      Projectivization.mk field second hsecondNe := by
    intro heq
    obtain ⟨coefficient, hcoefficient⟩ := (Projectivization.mk_eq_mk_iff' field _ _ _ _).mp heq
    have hzero : (1 : field) • first + (-coefficient) • second = 0 := by
      rw [one_smul, neg_smul, hcoefficient]
      exact add_neg_cancel first
    exact one_ne_zero (hindependent 1 (-coefficient) hzero).1
  exact ⟨Projectivization.mk field first hfirstNe, Projectivization.mk field second hsecondNe,
    hpointsNe, eigenbasis_distinct_scalars_fixed_points equivalence first second hfirstNe hsecondNe
      firstScalar secondScalar hscalarNe hfirstEigen hsecondEigen hindependent hspan⟩

end CFSG.RankThreeEvenClassification.Helpers
