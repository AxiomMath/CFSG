module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormSimilitude

public section

namespace CFSG.ComponentClassification.CatalogueBGraphForm

noncomputable section

universe u

abbrev fixedPGL (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) : Subgroup (Matrix.ProjGenLinGroup (Fin n) K) :=
  TauCeti.fixedSubgroup (pglPureGraphAction n K A).toMonoidHom

theorem graph_scalar_equation_iff (n : ℕ) (K : Type u) [Field K]
    (A g : Matrix.GeneralLinearGroup (Fin n) K) (mu : Kˣ) :
    (A * glGraphAut n K g * A⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin n) mu = g ↔
      glTranspose n K g * A⁻¹ * g = A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) mu := by
  constructor
  · intro h
    calc
      _ = glTranspose n K g * A⁻¹ *
          ((A * glGraphAut n K g * A⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin n) mu) := by rw [h]
      _ = _ := by unfold glTranspose; group
  · intro h
    calc
      _ = A * glGraphAut n K g *
          (A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) mu) := by group
      _ = A * glGraphAut n K g * (glTranspose n K g * A⁻¹ * g) := by rw [h]
      _ = g := by unfold glTranspose; group

theorem projective_fixed_iff_similitude (n : ℕ) (K : Type u) [Field K]
    (A g : Matrix.GeneralLinearGroup (Fin n) K) :
    Matrix.ProjGenLinGroup.mk g ∈ fixedPGL n K A ↔ g ∈ similitudeGroup n K A⁻¹ := by
  change pglPureGraphAction n K A (Matrix.ProjGenLinGroup.mk g) = Matrix.ProjGenLinGroup.mk g ↔ _
  rw [pglPureGraphAction_mk, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  change (∃ mu : Kˣ,
    (A * glGraphAut n K g * A⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin n) mu = g) ↔
      ∃ mu : Kˣ, glTranspose n K g * A⁻¹ * g =
        A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) mu
  exact exists_congr (graph_scalar_equation_iff n K A g)

theorem projective_fixed_iff_matrix_similitude (n : ℕ) (K : Type u) [Field K]
    (A g : Matrix.GeneralLinearGroup (Fin n) K) :
    Matrix.ProjGenLinGroup.mk g ∈ fixedPGL n K A ↔
      ∃ mu : Kˣ, g.val.transpose * (A⁻¹).val * g.val = mu.val • (A⁻¹).val :=
  (projective_fixed_iff_similitude n K A g).trans (mem_similitudeGroup n K A⁻¹ g)

theorem fixedPGL_eq_similitude_image (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    fixedPGL n K A = (similitudeGroup n K A⁻¹).map Matrix.ProjGenLinGroup.mk := by
  ext x
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  constructor
  · intro h
    exact ⟨g, (projective_fixed_iff_similitude n K A g).mp h, rfl⟩
  · rintro ⟨h, hh, heq⟩
    rw [← heq]
    exact (projective_fixed_iff_similitude n K A h).mpr hh

@[expose] def similitudeProjection (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    similitudeGroup n K A⁻¹ →* fixedPGL n K A :=
  (Matrix.ProjGenLinGroup.mk.comp (similitudeGroup n K A⁻¹).subtype).codRestrict _
    (fun g => (projective_fixed_iff_similitude n K A g.val).mpr g.property)

theorem similitudeProjection_val (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (g : similitudeGroup n K A⁻¹) :
    (similitudeProjection n K A g).val = Matrix.ProjGenLinGroup.mk g.val := rfl

theorem similitudeProjection_surjective (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) : Function.Surjective (similitudeProjection n K A) := by
  intro x
  obtain ⟨g, hg⟩ := Matrix.ProjGenLinGroup.mk_surjective x.val
  refine ⟨⟨g, (projective_fixed_iff_similitude n K A g).mp ?_⟩, Subtype.ext hg⟩
  rw [hg]
  exact x.property

theorem scalar_mem_similitude (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ similitudeGroup n K R := by
  refine ⟨c ^ 2, ?_⟩
  rw [glTranspose_scalar, Matrix.GeneralLinearGroup.scalar_commute, mul_assoc,
    ← map_mul, ← pow_two]

@[expose] def similitudeScalars (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) : Kˣ →* similitudeGroup n K R :=
  (Matrix.GeneralLinearGroup.scalar (Fin n)).codRestrict _ (scalar_mem_similitude n K R)

theorem similitudeScalars_val (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (c : Kˣ) :
    (similitudeScalars n K R c).val = Matrix.GeneralLinearGroup.scalar (Fin n) c := rfl

theorem similitudeMultiplier_scalar (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (c : Kˣ) :
    similitudeMultiplierHom n K R (similitudeScalars n K R c) = c ^ 2 := by
  apply similitudeMultiplier_unique
  change glTranspose n K (Matrix.GeneralLinearGroup.scalar (Fin n) c) * R *
    Matrix.GeneralLinearGroup.scalar (Fin n) c = R * Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ 2)
  rw [glTranspose_scalar, Matrix.GeneralLinearGroup.scalar_commute, mul_assoc,
    ← map_mul, ← pow_two]

theorem similitudeScalars_range_central (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) :
    (similitudeScalars n K R).range ≤ Subgroup.center (similitudeGroup n K R) := by
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact (Matrix.GeneralLinearGroup.scalar_commute c g.val).symm

theorem similitudeProjection_kernel (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (similitudeProjection n K A).ker = (similitudeScalars n K A⁻¹).range := by
  ext g
  constructor
  · intro hg
    have hmk : Matrix.ProjGenLinGroup.mk g.val = 1 := congrArg Subtype.val hg
    have hc := Matrix.ProjGenLinGroup.mk_eq_one.mp hmk
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, rfl⟩
    apply Subtype.ext
    exact Matrix.ProjGenLinGroup.mk_scalar c

theorem similitudeProjection_central_kernel (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (similitudeProjection n K A).ker ≤ Subgroup.center (similitudeGroup n K A⁻¹) := by
  rw [similitudeProjection_kernel]
  exact similitudeScalars_range_central n K A⁻¹

@[expose] def similitudeScalarQuotientEquivFixedPGL (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (similitudeGroup n K A⁻¹ ⧸ (similitudeProjection n K A).ker) ≃* fixedPGL n K A :=
  QuotientGroup.quotientKerEquivOfSurjective _ (similitudeProjection_surjective n K A)

end

end CFSG.ComponentClassification.CatalogueBGraphForm
