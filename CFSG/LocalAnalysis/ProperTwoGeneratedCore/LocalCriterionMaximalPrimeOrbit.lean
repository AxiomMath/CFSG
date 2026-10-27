module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem conjugacyWithin_card_le [Finite G] {A B : Subgroup G} (hAB : A ≤ B) (s : G) :
    Nat.card (conjugacyWithin A s) ≤ Nat.card (conjugacyWithin B s) := by
  apply Nat.card_le_card_of_injective
    (f := fun x : conjugacyWithin A s =>
      (⟨x.val, by obtain ⟨a, ha⟩ := x.property; exact ⟨⟨a.val, hAB a.property⟩, ha⟩⟩ :
        conjugacyWithin B s))
  intro a b hab
  exact Subtype.ext (congrArg (fun x : conjugacyWithin B s => x.val) hab)

theorem equal_orbit_card_centralizer_product [Finite G]
    (M R : Subgroup G) (hMR : M ≤ R) (s : G)
    (hcard : Nat.card (conjugacyWithin M s) = Nat.card (conjugacyWithin R s)) :
    ∀ r ∈ R, ∃ c ∈ R ⊓ Subgroup.centralizer ({s} : Set G), ∃ m ∈ M, c * m = r := by
  have hsubset : conjugacyWithin M s ⊆ conjugacyWithin R s := by
    rintro x ⟨a, ha⟩
    exact ⟨⟨a.val, hMR a.property⟩, ha⟩
  have heq : conjugacyWithin M s = conjugacyWithin R s := by
    apply Set.eq_of_subset_of_ncard_le hsubset
    exact hcard.ge
  intro r hr
  have hconj : r⁻¹ * s * r ∈ conjugacyWithin R s := ⟨⟨r, hr⟩, rfl⟩
  rw [← heq] at hconj
  obtain ⟨m, hm⟩ := hconj
  refine ⟨r * (m : G)⁻¹, ⟨R.mul_mem hr (R.inv_mem (hMR m.property)), ?_⟩,
    m, m.property, by group⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hc := (right_conjugates_eq_iff (z := s) (a := (m : G)) (b := r)).mp hm
  have hcinv := (Subgroup.centralizer ({s} : Set G)).inv_mem hc
  apply Subgroup.mem_centralizer_singleton_iff.mp
  simpa only [mul_inv_rev, inv_inv] using hcinv

theorem equal_orbit_card_normalizes_intermediate [Finite G]
    (M U R : Subgroup G) (hMU : M ≤ U) (hUR : U ≤ R) (s : G)
    (hsR : s ∈ Subgroup.normalizer (R : Set G))
    (hsM : s ∈ Subgroup.normalizer (M : Set G))
    (hcard : Nat.card (conjugacyWithin M s) = Nat.card (conjugacyWithin R s)) :
    s ∈ Subgroup.normalizer (U : Set G) := by
  have hconj (u : G) (hu : u ∈ U) : s * u * s⁻¹ ∈ U := by
    obtain ⟨c, hc, m, hm, hcm⟩ := equal_orbit_card_centralizer_product M R
      (hMU.trans hUR) s hcard u (hUR hu)
    have hcU : c ∈ U := by
      have hx := U.mul_mem hu (U.inv_mem (hMU hm))
      rw [← hcm] at hx
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hx
    have hcs : Commute c s := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hmconj : s * m * s⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hsM m).mp hm
    rw [← hcm]
    have heq : s * (c * m) * s⁻¹ = c * (s * m * s⁻¹) := by
      rw [← mul_assoc s c m, ← hcs.eq]
      simp only [mul_assoc]
    rw [heq]
    exact U.mul_mem hcU (hMU hmconj)
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · exact hconj u
  · intro hu
    have hconjuR : s * u * s⁻¹ ∈ R := hUR hu
    have huR : u ∈ R := (Subgroup.mem_normalizer_iff.mp hsR u).mpr hconjuR
    obtain ⟨c, hc, m, hm, hcm⟩ := equal_orbit_card_centralizer_product M R
      (hMU.trans hUR) s hcard u huR
    have hcs : Commute c s := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hmconj : s * m * s⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hsM m).mp hm
    have hprod : s * u * s⁻¹ = c * (s * m * s⁻¹) := by
      rw [← hcm]
      rw [← mul_assoc s c m, ← hcs.eq]
      simp only [mul_assoc]
    have hcU : c ∈ U := by
      have hx := U.mul_mem hu (U.inv_mem (hMU hmconj))
      rw [hprod] at hx
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hx
    rw [← hcm]
    exact U.mul_mem hcU (hMU hm)

theorem pointFixedSet_eq_pair_of_card_le_two [Finite G]
    (H Q : Subgroup G) (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (ha : a ∈ pointFixedSet H Q) (hb : b ∈ pointFixedSet H Q)
    (hcard : Nat.card (pointFixedSet H Q) ≤ 2) : pointFixedSet H Q = {a, b} := by
  have hsub : ({a, b} : Set (pointRightCosetSpace H)) ⊆ pointFixedSet H Q := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  symm
  apply Set.eq_of_subset_of_ncard_le hsub
  simpa [Set.ncard_insert_of_notMem, hab] using hcard

theorem no_fixed_point_involution_swaps_pair
    (H : Subgroup G) (s : G) (hs : orderOf s = 2)
    (a b : pointRightCosetSpace H)
    (hstable : pointRightCosetMul H a s ∈ ({a, b} : Set (pointRightCosetSpace H)))
    (hno : pointRightCosetMul H a s ≠ a) :
    pointRightCosetMul H a s = b ∧ pointRightCosetMul H b s = a := by
  have heq : pointRightCosetMul H a s = b := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, hno, false_or] using hstable
  refine ⟨heq, ?_⟩
  have hss : s * s = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hs).1
  rw [← heq, pointRightCosetMul_mul, hss, pointRightCosetMul_one]

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
