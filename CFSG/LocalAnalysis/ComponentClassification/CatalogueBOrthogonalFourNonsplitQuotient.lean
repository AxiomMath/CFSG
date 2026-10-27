module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitNormal

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

open scoped commutatorElement

universe u

variable {K : Type u} [Field K] [Finite K] (delta : K) [Fact (¬ IsSquare delta)]

abbrev SpecialQuotient (h2 : (2 : K) ≠ 0) :=
  HermitianIsometries delta ⧸ specialImage delta h2

@[expose] def quotientCongruenceImage (h2 : (2 : K) ≠ 0) :
    Subgroup (SpecialQuotient delta h2) :=
  (congruenceImage delta h2).map (QuotientGroup.mk' (specialImage delta h2))

instance quotientCongruenceImageNormal (h2 : (2 : K) ≠ 0) :
    (quotientCongruenceImage delta h2).Normal :=
  (congruenceImageNormal delta h2).map _ (QuotientGroup.mk'_surjective _)

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem domainDeterminant_commutator (A B : normDeterminantOne delta) :
    domainDeterminant delta ⁅A, B⁆ = 1 := by
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem congruence_commutator_mem_specialImage (h2 : (2 : K) ≠ 0)
    {g h : HermitianIsometries delta} (hg : g ∈ congruenceImage delta h2)
    (hh : h ∈ congruenceImage delta h2) : ⁅g, h⁆ ∈ specialImage delta h2 := by
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨B, rfl⟩ := hh
  rw [← map_commutatorElement]
  exact rho_mem_specialImage_of_determinant delta h2 _ (domainDeterminant_commutator delta A B)

theorem quotientCongruenceImage_mul_comm (h2 : (2 : K) ≠ 0)
    {g h : SpecialQuotient delta h2} (hg : g ∈ quotientCongruenceImage delta h2)
    (hh : h ∈ quotientCongruenceImage delta h2) : g * h = h * g := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hh
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr (congruence_commutator_mem_specialImage delta h2 ha hb)

instance quotientCongruenceImageCommutative (h2 : (2 : K) ≠ 0) :
    IsMulCommutative (quotientCongruenceImage delta h2) :=
  IsMulCommutative.of_setLike_mul_comm (fun _ ha _ hb =>
    quotientCongruenceImage_mul_comm delta h2 ha hb)

theorem quotientCongruenceImage_index (h2 : (2 : K) ≠ 0) :
    (quotientCongruenceImage delta h2).index = (congruenceImage delta h2).index := by
  apply Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact specialImage_le_congruenceImage delta h2

theorem quotientCongruenceImage_index_dvd_two (h2 : (2 : K) ≠ 0) :
    (quotientCongruenceImage delta h2).index ∣ 2 := by
  rw [quotientCongruenceImage_index]
  exact congruenceImage_index_dvd_two delta h2

theorem quotientCongruenceImage_index_le_two (h2 : (2 : K) ≠ 0) :
    (quotientCongruenceImage delta h2).index ≤ 2 :=
  Nat.le_of_dvd (by decide) (quotientCongruenceImage_index_dvd_two delta h2)

instance quotientByCongruenceImageCyclic (h2 : (2 : K) ≠ 0) :
    IsCyclic (SpecialQuotient delta h2 ⧸ quotientCongruenceImage delta h2) := by
  apply isCyclic_of_card_dvd_prime (p := 2)
  exact quotientCongruenceImage_index_dvd_two delta h2

instance specialQuotientSolvable (h2 : (2 : K) ≠ 0) :
    Group.IsSolvable (SpecialQuotient delta h2) :=
  Group.isSolvable_of_subgroup_quotient (quotientCongruenceImage delta h2)

theorem hermitian_isometry_quotient_structure (h2 : (2 : K) ≠ 0) :
    ∃ A : Subgroup (SpecialQuotient delta h2), A.Normal ∧ IsMulCommutative A ∧
      A.index ≤ 2 ∧ Group.IsSolvable (SpecialQuotient delta h2) :=
  ⟨quotientCongruenceImage delta h2, inferInstance, inferInstance,
    quotientCongruenceImage_index_le_two delta h2, inferInstance⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
