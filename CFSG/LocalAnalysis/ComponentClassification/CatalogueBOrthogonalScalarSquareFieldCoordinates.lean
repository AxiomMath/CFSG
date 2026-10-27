module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldBasic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

@[expose] def coordinateElement (T : Module.End K V) (a b : K) : scalarAlgebra T :=
  algebraMap K (scalarAlgebra T) a + b • generator T

theorem coordinateElement_val (T : Module.End K V) (a b : K) :
    (coordinateElement T a b).val = algebraMap K (Module.End K V) a + b • T := rfl

theorem coordinateElement_zero (T : Module.End K V) : coordinateElement T 0 0 = 0 := by
  simp only [coordinateElement, map_zero, zero_smul, add_zero]

theorem coordinateElement_one (T : Module.End K V) : coordinateElement T 1 0 = 1 := by
  simp only [coordinateElement, map_one, zero_smul, add_zero]

theorem coordinateElement_generator (T : Module.End K V) :
    coordinateElement T 0 1 = generator T := by
  simp only [coordinateElement, map_zero, one_smul, zero_add]

theorem scalarBasis_expansion [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (z : scalarAlgebra T) :
    coordinateElement T ((scalarBasis T d hns hsquare).repr z 0)
      ((scalarBasis T d hns hsquare).repr z 1) = z := by
  have h := (scalarBasis T d hns hsquare).sum_repr z
  rw [Fin.sum_univ_two, scalarBasis_zero, scalarBasis_one] at h
  simpa only [coordinateElement, Algebra.algebraMap_eq_smul_one] using h

theorem coordinateElement_repr [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) :
    (scalarBasis T d hns hsquare).repr (coordinateElement T a b) =
      Finsupp.single 0 a + Finsupp.single 1 b := by
  rw [coordinateElement, Algebra.algebraMap_eq_smul_one,
    ← scalarBasis_zero T d hns hsquare, ← scalarBasis_one T d hns hsquare]
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem coordinateElement_eq_iff [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b c e : K) :
    coordinateElement T a b = coordinateElement T c e ↔ a = c ∧ b = e := by
  constructor
  · intro h
    have hr := congrArg (scalarBasis T d hns hsquare).repr h
    rw [coordinateElement_repr, coordinateElement_repr] at hr
    constructor
    · simpa using congrArg (fun f : Fin 2 →₀ K => f 0) hr
    · simpa using congrArg (fun f : Fin 2 →₀ K => f 1) hr
  · rintro ⟨rfl, rfl⟩
    rfl

theorem coordinateElement_eq_zero_iff [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) : coordinateElement T a b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [← coordinateElement_zero T, coordinateElement_eq_iff T d hns hsquare]

theorem existsUnique_coordinates [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (z : scalarAlgebra T) :
    ∃! p : K × K, coordinateElement T p.1 p.2 = z := by
  refine ⟨⟨(scalarBasis T d hns hsquare).repr z 0,
    (scalarBasis T d hns hsquare).repr z 1⟩, scalarBasis_expansion T d hns hsquare z, ?_⟩
  intro p hp
  have h := (coordinateElement_eq_iff T d hns hsquare p.1 p.2
    ((scalarBasis T d hns hsquare).repr z 0) ((scalarBasis T d hns hsquare).repr z 1)).mp
      (hp.trans (scalarBasis_expansion T d hns hsquare z).symm)
  exact Prod.ext h.1 h.2

theorem mem_scalarAlgebra_iff [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (F : Module.End K V) :
    F ∈ scalarAlgebra T ↔ ∃ a b : K, F = algebraMap K (Module.End K V) a + b • T := by
  constructor
  · intro hF
    obtain ⟨p, hp, _⟩ := existsUnique_coordinates T d hns hsquare ⟨F, hF⟩
    exact ⟨p.1, p.2, (congrArg Subtype.val hp).symm⟩
  · rintro ⟨a, b, rfl⟩
    exact (coordinateElement T a b).property

theorem nonsquare_ne_zero (d : K) (hns : ¬ IsSquare d) : d ≠ 0 := by
  rintro rfl
  exact hns IsSquare.zero

theorem coordinate_denominator_ne_zero (d : K) (hns : ¬ IsSquare d) (a b : K)
    (hab : a ≠ 0 ∨ b ≠ 0) : a ^ 2 - d * b ^ 2 ≠ 0 := by
  intro hzero
  by_cases hb : b = 0
  · have ha : a = 0 := by simpa [hb] using hzero
    exact hab.elim (fun h => h ha) (fun h => h hb)
  · apply hns
    rw [isSquare_iff_exists_sq]
    refine ⟨a / b, ?_⟩
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hb)).mpr
    have h := sub_eq_zero.mp hzero
    exact h.symm

theorem coordinateElement_mul [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b c e : K) :
    coordinateElement T a b * coordinateElement T c e =
      coordinateElement T (a * c + d * b * e) (a * e + b * c) := by
  let := scalarField T d hns hsquare
  simp only [coordinateElement, Algebra.smul_def, map_add, map_mul]
  linear_combination (algebraMap K (scalarAlgebra T) b *
    algebraMap K (scalarAlgebra T) e) * generator_square T d hsquare

theorem coordinateElement_conjugate_product [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) :
    coordinateElement T a b * coordinateElement T a (-b) =
      algebraMap K (scalarAlgebra T) (a ^ 2 - d * b ^ 2) := by
  rw [coordinateElement_mul T d hns hsquare]
  have h0 : a * (-b) + b * a = 0 := by ring
  have h1 : a * a + d * b * (-b) = a ^ 2 - d * b ^ 2 := by ring
  rw [h0, h1]
  simp only [coordinateElement, zero_smul, add_zero]

theorem coordinateElement_inv [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    letI := scalarField T d hns hsquare
    (coordinateElement T a b)⁻¹ = coordinateElement T a (-b) /
      algebraMap K (scalarAlgebra T) (a ^ 2 - d * b ^ 2) := by
  let := scalarField T d hns hsquare
  have hden : algebraMap K (scalarAlgebra T) (a ^ 2 - d * b ^ 2) ≠ 0 :=
    (map_ne_zero (algebraMap K (scalarAlgebra T))).mpr
      (coordinate_denominator_ne_zero d hns a b hab)
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_div_assoc, coordinateElement_conjugate_product T d hns hsquare, div_self hden]

theorem coordinateElement_inv_val [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    letI := scalarField T d hns hsquare
    ((coordinateElement T a b)⁻¹).val = (a ^ 2 - d * b ^ 2)⁻¹ •
      (algebraMap K (Module.End K V) a - b • T) := by
  let := scalarField T d hns hsquare
  rw [coordinateElement_inv T d hns hsquare a b hab, div_eq_mul_inv, ← map_inv₀]
  rw [mul_comm, ← Algebra.smul_def]
  change (a ^ 2 - d * b ^ 2)⁻¹ • (coordinateElement T a (-b)).val = _
  rw [coordinateElement_val, neg_smul]
  simp only [sub_eq_add_neg]

theorem coordinate_operator_inverse [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    let R := algebraMap K (Module.End K V) a + b • T
    let S := (a ^ 2 - d * b ^ 2)⁻¹ • (algebraMap K (Module.End K V) a - b • T)
    R * S = 1 ∧ S * R = 1 := by
  let := scalarField T d hns hsquare
  have hn : coordinateElement T a b ≠ 0 := by
    intro hz
    have hz' := (coordinateElement_eq_zero_iff T d hns hsquare a b).mp hz
    exact hab.elim (fun h => h hz'.1) (fun h => h hz'.2)
  have hleft := congrArg Subtype.val (mul_inv_cancel₀ hn)
  have hright := congrArg Subtype.val (inv_mul_cancel₀ hn)
  change (coordinateElement T a b).val * ((coordinateElement T a b)⁻¹).val = 1 at hleft
  change ((coordinateElement T a b)⁻¹).val * (coordinateElement T a b).val = 1 at hright
  rw [coordinateElement_inv_val T d hns hsquare a b hab] at hleft hright
  exact ⟨hleft, hright⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
