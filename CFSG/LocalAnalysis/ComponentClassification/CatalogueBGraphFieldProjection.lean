module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometry

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHermitian CatalogueBUnitaryIsometry
open CFSG.LieType.Universal.Unitary

universe u

theorem graphField_eq_inverse_conjugateTranspose (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    glGraphFieldAut n K sigma g = (conjugateTransposeGL sigma g)⁻¹ := by
  rw [← graphField_inverse_eq_conjugateTranspose, ← map_inv, inv_inv]

theorem graphField_scalar_equation_iff (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) (mu : Kˣ) :
    glGraphFieldAut n K sigma g * GeneralLinearGroup.scalar (Fin n) mu = g ↔
      conjugateTransposeGL sigma g * g = GeneralLinearGroup.scalar (Fin n) mu := by
  rw [graphField_eq_inverse_conjugateTranspose]
  constructor
  · intro h
    have h' := congrArg (fun x : GL (Fin n) K => conjugateTransposeGL sigma g * x) h
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h'.symm
  · intro h
    have h' := congrArg (fun x : GL (Fin n) K => (conjugateTransposeGL sigma g)⁻¹ * x) h
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h'.symm

theorem projective_fixed_iff_multiplier (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    ProjGenLinGroup.mk g ∈ fixedPGL n K sigma ↔
      ∃ mu : Kˣ, conjugateTransposeGL sigma g * g = GeneralLinearGroup.scalar (Fin n) mu := by
  change pglGraphFieldAut n K sigma (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk g ↔ _
  rw [pglGraphFieldAut_mk, ProjGenLinGroup.mk_eq_mk_iff]
  exact exists_congr (graphField_scalar_equation_iff n K sigma g)

theorem projective_fixed_iff_matrix_multiplier (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    ProjGenLinGroup.mk g ∈ fixedPGL n K sigma ↔
      ∃ mu : Kˣ, conjTr sigma g.val * g.val = Matrix.scalar (Fin n) mu.val := by
  rw [projective_fixed_iff_multiplier]
  apply exists_congr
  intro mu
  rw [Units.ext_iff]
  rfl

theorem graphField_multiplier_fixed (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1)
    (g : GL (Fin n) K) (mu : Kˣ)
    (hmu : conjugateTransposeGL sigma g * g = GeneralLinearGroup.scalar (Fin n) mu) :
    sigma (mu : K) = mu := by
  have hstar := congrArg (conjugateTransposeGL sigma) hmu
  rw [conjugateTransposeGL_mul, conjugateTransposeGL_involutive n K sigma hsigma,
    conjugateTransposeGL_scalar, hmu] at hstar
  let i : Fin n := ⟨0, by omega⟩
  have hentry := congrArg (fun M : GL (Fin n) K => M i i) hstar
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at hentry
  change (mu : K) = sigma (mu : K) at hentry
  exact hentry.symm

theorem graphField_fixed_iff_unitary (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    glGraphFieldAut n K sigma g = g ↔ g ∈ Uid sigma n := by
  rw [mem_Uid_iff]
  have h : conjTr sigma g.val * g.val = 1 ↔ conjugateTransposeGL sigma g * g = 1 := by
    constructor
    · intro h
      exact Units.ext h
    · intro h
      exact congrArg Units.val h
  rw [h, graphField_eq_inverse_conjugateTranspose]
  exact inv_eq_iff_eq_inv.trans mul_eq_one_iff_eq_inv.symm

theorem exists_unitary_scalar_multiple (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (g : GL (Fin n) K) (mu : Kˣ)
    (hmu : conjugateTransposeGL sigma g * g = GeneralLinearGroup.scalar (Fin n) mu) :
    ∃ b : Kˣ, GeneralLinearGroup.scalar (Fin n) b * g ∈ Uid sigma n := by
  have hfixed := graphField_multiplier_fixed n K hn sigma hsigma g mu hmu
  have hinvfixed : sigma (mu⁻¹ : Kˣ) = (mu⁻¹ : Kˣ) := by
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hfixed]
  obtain ⟨b, hb⟩ := CatalogueBLinearTwoDescent.exists_norm_unit K sigma hsigma hne mu⁻¹ hinvfixed
  have hnorm : Units.map sigma.toMonoidHom b * b = mu⁻¹ := by
    apply Units.ext
    change sigma (b : K) * (b : K) = (mu⁻¹ : Kˣ)
    simpa only [mul_comm] using hb
  refine ⟨b, (mem_Uid_iff sigma n _).mpr ?_⟩
  have hproduct : conjugateTransposeGL sigma (GeneralLinearGroup.scalar (Fin n) b * g) *
      (GeneralLinearGroup.scalar (Fin n) b * g) = 1 := by
    rw [conjugateTransposeGL_mul, conjugateTransposeGL_scalar]
    calc
      _ = conjugateTransposeGL sigma g *
          (GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom b) *
            GeneralLinearGroup.scalar (Fin n) b) * g := by group
      _ = GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom b * b) *
          (conjugateTransposeGL sigma g * g) := by
        rw [← map_mul,
          ← GeneralLinearGroup.scalar_commute (Units.map sigma.toMonoidHom b * b)
            (conjugateTransposeGL sigma g), mul_assoc]
      _ = 1 := by rw [hmu, ← map_mul, hnorm, inv_mul_cancel, map_one]
  exact congrArg Units.val hproduct

@[expose] def unitaryProjection (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Uid sigma n →* fixedPGL n K sigma :=
  (ProjGenLinGroup.mk.comp (Uid sigma n).subtype).codRestrict _ (fun g => by
    change pglGraphFieldAut n K sigma (ProjGenLinGroup.mk g.val) = ProjGenLinGroup.mk g.val
    rw [pglGraphFieldAut_mk, (graphField_fixed_iff_unitary n K sigma g.val).mpr g.property])

theorem unitaryProjection_val (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : Uid sigma n) :
    (unitaryProjection n K sigma g).val = ProjGenLinGroup.mk g.val := rfl

theorem unitaryProjection_surjective (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    Function.Surjective (unitaryProjection n K sigma) := by
  intro x
  obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective x.val
  have hfixed : ProjGenLinGroup.mk g ∈ fixedPGL n K sigma := hg.symm ▸ x.property
  obtain ⟨mu, hmu⟩ := (projective_fixed_iff_multiplier n K sigma g).mp hfixed
  obtain ⟨b, hb⟩ := exists_unitary_scalar_multiple n K hn sigma hsigma hne g mu hmu
  refine ⟨⟨GeneralLinearGroup.scalar (Fin n) b * g, hb⟩, Subtype.ext ?_⟩
  change ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin n) b * g) = x.val
  rw [map_mul, ProjGenLinGroup.mk_scalar, one_mul, hg]

theorem fixedPGL_eq_unitary_image (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    fixedPGL n K sigma = (Uid sigma n).map ProjGenLinGroup.mk := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := unitaryProjection_surjective n K hn sigma hsigma hne ⟨x, hx⟩
    exact ⟨g.val, g.property, congrArg Subtype.val hg⟩
  · rintro ⟨g, hg, rfl⟩
    exact (unitaryProjection n K sigma ⟨g, hg⟩).property

theorem unitaryProjection_kernel_iff (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : Uid sigma n) :
    g ∈ (unitaryProjection n K sigma).ker ↔
      ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = g.val := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hc := ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val h)
    rwa [GeneralLinearGroup.center_eq_range_scalar] at hc
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    change ProjGenLinGroup.mk g.val = 1
    rw [← hc, ProjGenLinGroup.mk_scalar]

theorem scalar_mem_unitary_iff (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈ Uid sigma n ↔ sigma (c : K) * (c : K) = 1 := by
  rw [← graphField_fixed_iff_unitary, graphField_eq_inverse_conjugateTranspose,
    conjugateTransposeGL_scalar]
  constructor
  · intro h
    have hprod : GeneralLinearGroup.scalar (Fin n)
        (Units.map sigma.toMonoidHom c * c) = 1 := by
      rw [map_mul]
      exact mul_eq_one_iff_eq_inv.mpr (inv_eq_iff_eq_inv.mp h)
    let i : Fin n := ⟨0, by omega⟩
    have hentry := congrArg (fun M : GL (Fin n) K => M i i) hprod
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply, ite_true,
      Units.val_mul, Units.coe_map] at hentry
    change sigma (c : K) * (c : K) = 1 at hentry
    exact hentry
  · intro h
    have hu : Units.map sigma.toMonoidHom c * c = 1 := Units.ext h
    have hprod := congrArg (GeneralLinearGroup.scalar (Fin n)) hu
    rw [map_mul, map_one] at hprod
    exact inv_eq_iff_eq_inv.mpr (mul_eq_one_iff_eq_inv.mp hprod)

theorem unitaryProjection_kernel_norm_one (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (g : Uid sigma n) :
    g ∈ (unitaryProjection n K sigma).ker ↔
      ∃ c : Kˣ, sigma (c : K) * (c : K) = 1 ∧
        GeneralLinearGroup.scalar (Fin n) c = g.val := by
  rw [unitaryProjection_kernel_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (scalar_mem_unitary_iff n K hn sigma c).mp (hc.symm ▸ g.property), hc⟩
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

theorem unitaryProjection_central_kernel (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    (unitaryProjection n K sigma).ker ≤ Subgroup.center (Uid sigma n) := by
  intro g hg
  obtain ⟨c, hc⟩ := (unitaryProjection_kernel_iff n K sigma g).mp hg
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  change h.val * g.val = g.val * h.val
  rw [← hc]
  exact (GeneralLinearGroup.scalar_commute c h.val).symm

@[expose] def unitaryScalarQuotientEquivFixedPGL (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    (Uid sigma n ⧸ (unitaryProjection n K sigma).ker) ≃* fixedPGL n K sigma :=
  QuotientGroup.quotientKerEquivOfSurjective _
    (unitaryProjection_surjective n K hn sigma hsigma hne)

end

end CFSG.ComponentClassification.CatalogueBGraphField
