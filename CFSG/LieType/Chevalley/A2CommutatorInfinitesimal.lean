module

public import CFSG.LieType.Chevalley.A2CommutatorCert

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootOps RootWalk

variable {τ : Tag} {R : Type*} [CommRing R]

theorem weylElt_mul_infE_mul_weylElt_neg
    (i j : Fin τ.rank) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * infE τ R j *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) =
      (signOf τ j i : R) • entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) := by
  rw [← entriesOp_entries_simple (simpleRow_eq_true τ) j]
  exact weylElt_mul_entriesOp_mul_inv (dataChecks τ) (val_lt_rootCertificate_length j) i

theorem weylElt_mul_infF_mul_weylElt_neg
    (i j : Fin τ.rank) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * infF τ R j *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) =
      (signOf τ (τ.rootCertificate.image j j) i : R) •
        entriesOp τ R (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) := by
  rw [← entriesOp_entries_neg_simple (simpleRow_eq_true τ) j]
  exact weylElt_mul_entriesOp_mul_inv (dataChecks τ)
    (rootCertificate_image_lt (val_lt_rootCertificate_length j) j) i

theorem weylElt_conj_pow
    (i : Fin τ.rank) (X : Module.End R (RootModule τ R)) (k : ℕ) :
    ((weylElt τ R i 1 : Module.End R (RootModule τ R)) * X *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R))) ^ k =
      (weylElt τ R i 1 : Module.End R (RootModule τ R)) * X ^ k *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) := by
  rw [← weylElt_inv, Units.conj_pow]

theorem infE_bracket_eq
    {i j : Fin τ.rank} (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    infE τ R i * infE τ R j - infE τ R j * infE τ R i =
      (weylElt τ R i 1 : Module.End R (RootModule τ R)) * infE τ R j *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) := by
  rw [weylElt_mul_infE_mul_weylElt_neg]
  exact (brackets_of_cartan hij hji).1

theorem infF_bracket_eq
    {i j : Fin τ.rank} (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    infF τ R i * infF τ R j - infF τ R j * infF τ R i =
      -((weylElt τ R i 1 : Module.End R (RootModule τ R)) * infF τ R j *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R))) := by
  rw [weylElt_mul_infF_mul_weylElt_neg, (brackets_of_cartan hij hji).2.1, Int.cast_neg]
  exact neg_smul (M := Module.End R (RootModule τ R)) _ _

theorem infF_bracket_eq_neg_one_smul
    {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) :
    infF τ R i * infF τ R j - infF τ R j * infF τ R i =
      (-1 : R) • ((weylElt τ R i 1 : Module.End R (RootModule τ R)) * infF τ R j *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R))) :=
  (infF_bracket_eq hij hji).trans (neg_one_smul R (M := Module.End R (RootModule τ R)) _).symm

variable (τ R) in
theorem a2_infinitesimal_relations
    (i j : Fin τ.rank) (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) :
    infE τ R i * infE τ R j - infE τ R j * infE τ R i =
        (weylElt τ R i 1 : Module.End R (RootModule τ R)) * infE τ R j *
          (weylElt τ R i (-1) : Module.End R (RootModule τ R)) ∧
      infF τ R i * infF τ R j - infF τ R j * infF τ R i =
        -((weylElt τ R i 1 : Module.End R (RootModule τ R)) * infF τ R j *
          (weylElt τ R i (-1) : Module.End R (RootModule τ R))) ∧
      infE τ R i * (infE τ R i * infE τ R j - infE τ R j * infE τ R i) =
        (infE τ R i * infE τ R j - infE τ R j * infE τ R i) * infE τ R i ∧
      infE τ R j * (infE τ R i * infE τ R j - infE τ R j * infE τ R i) =
        (infE τ R i * infE τ R j - infE τ R j * infE τ R i) * infE τ R j ∧
      infF τ R i * (infF τ R i * infF τ R j - infF τ R j * infF τ R i) =
        (infF τ R i * infF τ R j - infF τ R j * infF τ R i) * infF τ R i ∧
      infF τ R j * (infF τ R i * infF τ R j - infF τ R j * infF τ R i) =
        (infF τ R i * infF τ R j - infF τ R j * infF τ R i) * infF τ R j ∧
      (infE τ R i * infE τ R j - infE τ R j * infE τ R i) ^ 4 = 0 ∧
      (infF τ R i * infF τ R j - infF τ R j * infF τ R i) ^ 4 = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := brackets_of_cartan (R := R) hij hji
  refine ⟨infE_bracket_eq hij hji, infF_bracket_eq hij hji, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]
    exact (Commute.smul_right h3 _).eq
  · rw [h1]
    exact (Commute.smul_right h4 _).eq
  · rw [h2]
    exact (Commute.smul_right h5 _).eq
  · rw [h2]
    exact (Commute.smul_right h6 _).eq
  · rw [infE_bracket_eq hij hji, weylElt_conj_pow, infE_pow_eq_zero j le_rfl, mul_zero, zero_mul]
  · rw [infF_bracket_eq_neg_one_smul hij hji, smul_pow, weylElt_conj_pow,
      infF_pow_eq_zero j le_rfl, mul_zero, zero_mul, smul_zero]

end CFSG.LieType.Chevalley
