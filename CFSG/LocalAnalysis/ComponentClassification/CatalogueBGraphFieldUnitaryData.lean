module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldScalarFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldScalarUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldNonidentity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearInner CatalogueBUnitaryIsometry
open CatalogueBUnitaryTwo CFSG.LieType.Universal.Unitary

universe u

theorem unitary_field_card_square (K : Type u) (r e : ℕ)
    (hcard : Nat.card K = r ^ (2 * e)) : Nat.card K = (r ^ e) ^ 2 := by
  rw [← pow_mul, Nat.mul_comm e 2]
  exact hcard

theorem unitary_native_graph_field_representative (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    pglGraphFieldAut n K sigma (ProjGenLinGroup.mk g) =
        ProjGenLinGroup.mk (glGraphFieldAut n K sigma g) ∧
      (glGraphFieldAut n K sigma g).val =
        (sigma.toRingHom.mapMatrix (g⁻¹).val).transpose :=
  ⟨pglGraphFieldAut_mk n K sigma g, glGraphFieldAut_matrix n K sigma g⟩

theorem unitary_scalar_graph_field_representative (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    scalarPGLGraphFieldAut n K sigma (scalarProjection n K g) =
        scalarProjection n K (glGraphFieldAut n K sigma g) ∧
      (glGraphFieldAut n K sigma g).val =
        (sigma.toRingHom.mapMatrix (g⁻¹).val).transpose :=
  ⟨scalarPGLGraphFieldAut_mk n K sigma g, glGraphFieldAut_matrix n K sigma g⟩

theorem graph_field_fixed_projective_unitary_group_native
    (K : Type u) [Field K] [Finite K] (r e : ℕ) [Fact r.Prime]
    (_he : 1 ≤ e) (hcard : Nat.card K = r ^ (2 * e)) (n : ℕ) (hn : 2 ≤ n) :
    let sigma := unitaryFieldConjugation r e (unitary_field_card_square K r e hcard)
    (∀ x : K, sigma x = x ^ (r ^ e)) ∧
      pglGraphFieldAut n K sigma ^ 2 = 1 ∧ pglGraphFieldAut n K sigma ≠ 1 ∧
      fixedPGL n K sigma = (Uid sigma n).map ProjGenLinGroup.mk ∧
      Function.Surjective (unitaryProjection n K sigma) ∧
      (unitaryProjection n K sigma).ker ≤ Subgroup.center (Uid sigma n) ∧
      (∀ g : Uid sigma n, g ∈ (unitaryProjection n K sigma).ker ↔
        ∃ c : Kˣ, sigma (c : K) * (c : K) = 1 ∧
          GeneralLinearGroup.scalar (Fin n) c = g.val) ∧
      (fixedT n K sigma).Normal ∧
      Nonempty (fixedPSL n K sigma ≃* fixedT n K sigma) := by
  let sigma := unitaryFieldConjugation r e (unitary_field_card_square K r e hcard)
  obtain ⟨hsigma, hne, _⟩ := unitaryFieldConjugation_data r e (unitary_field_card_square K r e hcard)
  exact ⟨unitaryFieldConjugation_apply r e (unitary_field_card_square K r e hcard),
    pglGraphFieldAut_sq_eq_one n K sigma hsigma, pglGraphFieldAut_ne_one n K hn sigma,
    fixedPGL_eq_unitary_image n K (by omega) sigma hsigma hne,
    unitaryProjection_surjective n K (by omega) sigma hsigma hne,
    unitaryProjection_central_kernel n K sigma,
    unitaryProjection_kernel_norm_one n K (by omega) sigma,
    inferInstance, ⟨fixedPSLEquivT n K sigma⟩⟩

theorem graph_field_fixed_projective_unitary_group
    (K : Type u) [Field K] [Finite K] (r e : ℕ) [Fact r.Prime]
    (_he : 1 ≤ e) (hcard : Nat.card K = r ^ (2 * e)) (n : ℕ) (hn : 2 ≤ n) :
    let sigma := unitaryFieldConjugation r e (unitary_field_card_square K r e hcard)
    (∀ x : K, sigma x = x ^ (r ^ e)) ∧
      scalarPGLGraphFieldAut n K sigma ^ 2 = 1 ∧ scalarPGLGraphFieldAut n K sigma ≠ 1 ∧
      scalarFixedPGL n K sigma = (Uid sigma n).map (scalarProjection n K) ∧
      Function.Surjective (scalarUnitaryProjection n K sigma) ∧
      (scalarUnitaryProjection n K sigma).ker ≤ Subgroup.center (Uid sigma n) ∧
      (∀ g : Uid sigma n, g ∈ (scalarUnitaryProjection n K sigma).ker ↔
        ∃ c : Kˣ, sigma (c : K) * (c : K) = 1 ∧
          GeneralLinearGroup.scalar (Fin n) c = g.val) ∧
      scalarPSLRange n K = ((scalarProjection n K).comp SpecialLinearGroup.toGL).range ∧
      Function.Injective (scalarPSLInclusion n K) ∧
      (∀ g : SpecialLinearGroup (Fin n) K,
        scalarPSLInclusion n K ((QuotientGroup.mk' (slScalarCenter n K)) g) =
          scalarProjection n K (SpecialLinearGroup.toGL g)) ∧
      (∀ x : ScalarProjectiveSpecialLinear n K,
        scalarPSLInclusion n K (scalarGraphFieldAut n K sigma x) =
          scalarPGLGraphFieldAut n K sigma (scalarPSLInclusion n K x)) ∧
      (scalarFixedT n K sigma).Normal ∧
      Nonempty (TauCeti.fixedSubgroup (scalarGraphFieldAut n K sigma).toMonoidHom ≃*
        scalarFixedT n K sigma) ∧
      (∀ x : TauCeti.fixedSubgroup (scalarGraphFieldAut n K sigma).toMonoidHom,
        (scalarFixedPSLEquivT n K sigma x).val.val = scalarPSLInclusion n K x.val) := by
  let sigma := unitaryFieldConjugation r e (unitary_field_card_square K r e hcard)
  obtain ⟨hsigma, hne, _⟩ := unitaryFieldConjugation_data r e (unitary_field_card_square K r e hcard)
  exact ⟨unitaryFieldConjugation_apply r e (unitary_field_card_square K r e hcard),
    scalarPGLGraphFieldAut_sq n K sigma hsigma, scalarPGLGraphFieldAut_ne_one n K hn sigma,
    scalarFixedPGL_eq_unitary_image n K (by omega) sigma hsigma hne,
    scalarUnitaryProjection_surjective n K (by omega) sigma hsigma hne,
    scalarUnitaryProjection_central_kernel n K sigma,
    scalarUnitaryProjection_kernel_norm_one n K (by omega) sigma,
    scalarPSLRange_eq_original_image n K, scalarPSLInclusion_injective n K,
    scalarPSLInclusion_mk n K, scalarPSLInclusion_graphField n K sigma,
    inferInstance, ⟨scalarFixedPSLEquivT n K sigma⟩, scalarFixedPSLEquivT_val n K sigma⟩

abbrev UnitaryDataProjectiveSpecial (n : ℕ) (K : Type u) [Field K] [Finite K]
    (r e : ℕ) [Fact r.Prime] (hcard : Nat.card K = (r ^ e) ^ 2) :=
  ProjectiveSpecialUnitary n K (unitaryFieldConjugation r e hcard)

theorem unitary_data_special_scalar_kernel (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (r e : ℕ) [Fact r.Prime] (hcard : Nat.card K = (r ^ e) ^ 2)
    (g : SUid (unitaryFieldConjugation r e hcard) n) :
    g ∈ specialUnitaryScalars n K (unitaryFieldConjugation r e hcard) ↔
      ∃ c : Kˣ, (c : K) * (c : K) ^ (r ^ e) = 1 ∧ (c : K) ^ n = 1 ∧
        GeneralLinearGroup.scalar (Fin n) c = g.val := by
  rw [specialUnitaryScalars_mem_iff n K hn]
  simp only [unitaryFieldConjugation_apply, mul_comm ((_) ^ (r ^ e))]

end

end CFSG.ComponentClassification.CatalogueBGraphField
