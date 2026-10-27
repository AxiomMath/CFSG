module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructureNormal

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open scoped commutatorElement

universe u

variable {K : Type u} [Field K]

abbrev SixSpecialQuotient (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :=
  SixIsometries delta ⧸ sixSpecialImage delta h2

@[expose] def sixQuotientKappaImage (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : Subgroup (SixSpecialQuotient delta h2) :=
  (kappa delta h2).range.map (QuotientGroup.mk' (sixSpecialImage delta h2))

instance sixQuotientKappaImageNormal (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : (sixQuotientKappaImage delta h2).Normal :=
  (sixKappaRangeNormal delta h2).map _ (QuotientGroup.mk'_surjective _)

theorem six_multiplier_commutator (delta : K) (g h : sixSimilitudes delta) :
    sixMultiplier delta ⁅g, h⁆ = 1 := by
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem six_kappa_commutator_mem_specialImage (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) {g h : SixIsometries delta}
    (hg : g ∈ (kappa delta h2).range) (hh : h ∈ (kappa delta h2).range) :
    ⁅g, h⁆ ∈ sixSpecialImage delta h2 := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hh
  rw [← map_commutatorElement]
  exact six_kappa_mem_specialImage_of_multiplier delta h2 _
    (six_multiplier_commutator delta a b)

theorem sixQuotientKappaImage_mul_comm (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) {g h : SixSpecialQuotient delta h2}
    (hg : g ∈ sixQuotientKappaImage delta h2) (hh : h ∈ sixQuotientKappaImage delta h2) :
    g * h = h * g := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hh
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (six_kappa_commutator_mem_specialImage delta h2 ha hb)

instance sixQuotientKappaImageCommutative (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : IsMulCommutative (sixQuotientKappaImage delta h2) :=
  IsMulCommutative.of_setLike_mul_comm
    (fun _ hg _ hh => sixQuotientKappaImage_mul_comm delta h2 hg hh)

theorem sixQuotientKappaImage_index (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) :
    (sixQuotientKappaImage delta h2).index = (kappa delta h2).range.index := by
  apply Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact sixSpecialImage_le_kappaRange delta h2

theorem sixQuotientKappaImage_index_dvd_two (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : (sixQuotientKappaImage delta h2).index ∣ 2 := by
  rw [sixQuotientKappaImage_index]
  exact six_kappa_range_index_dvd_two delta h2

theorem sixQuotientKappaImage_index_le_two (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : (sixQuotientKappaImage delta h2).index ≤ 2 :=
  Nat.le_of_dvd (by decide) (sixQuotientKappaImage_index_dvd_two delta h2)

instance sixQuotientByKappaImageCyclic (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) :
    IsCyclic (SixSpecialQuotient delta h2 ⧸ sixQuotientKappaImage delta h2) := by
  apply isCyclic_of_card_dvd_prime (p := 2)
  exact sixQuotientKappaImage_index_dvd_two delta h2

instance sixSpecialQuotientSolvable (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : Group.IsSolvable (SixSpecialQuotient delta h2) :=
  Group.isSolvable_of_subgroup_quotient (sixQuotientKappaImage delta h2)

theorem six_full_isometry_quotient_structure (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) :
    ∃ A : Subgroup (SixSpecialQuotient delta h2),
      A.Normal ∧ IsMulCommutative A ∧ A.index ≤ 2 ∧
        Group.IsSolvable (SixSpecialQuotient delta h2) :=
  ⟨sixQuotientKappaImage delta h2, inferInstance, inferInstance,
    sixQuotientKappaImage_index_le_two delta h2, inferInstance⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
