module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G]

theorem pair_first_centralizer_eq (D : Subgroup G) (u t : G) :
    (D ⊓ Subgroup.centralizer ({u} : Set G)) ⊓
        Subgroup.centralizer ({t} : Set G) =
      D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G) := by
  rw [denominatorFourGroup, Subgroup.centralizer_closure]
  ext c
  constructor
  · rintro ⟨⟨hcD, hcu⟩, hct⟩
    refine ⟨hcD, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hcu).symm
    · have hxt : x = t := Set.mem_singleton_iff.mp hx
      subst x
      exact (Subgroup.mem_centralizer_singleton_iff.mp hct).symm
  · rintro ⟨hcD, hc⟩
    exact ⟨⟨hcD, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hc u (by simp)).symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hc t (by simp)).symm⟩

theorem odd_inverted_subgroup_trivial_centralizer
    (T : Subgroup G) (t : G) (hodd : Odd (Nat.card T))
    (hinv : ∀ x ∈ T, rightConjugateElem x t = x⁻¹) :
    T ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  by_cases hxone : x = 1
  · exact Subgroup.mem_bot.mpr hxone
  · have hxodd : Odd (orderOf x) := by
      have h := hodd.of_dvd_nat (orderOf_dvd_natCard (⟨x, hx.1⟩ : T))
      exact (Subgroup.orderOf_coe (⟨x, hx.1⟩ : T)) ▸ h
    exact False.elim (odd_inverted_element_not_commute x t hxone hxodd (hinv x hx.1)
      (Subgroup.mem_centralizer_singleton_iff.mp hx.2))

variable [Finite G]

theorem original_pair_first_centralizer_product_index
    (H : Subgroup G) (a b : pointRightCosetSpace H)
    (u t : G) (ht : orderOf t = 2)
    (hflip : pointRightCosetMul H a t = b)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal)
    (htL : t ∈ L)
    (hodd : Odd (Nat.card (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G)))
    (hinv : ∀ x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b),
      rightConjugateElem x t = x⁻¹) :
    let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    let T := L ⊓ D
    involutionOrbit A t = involutionOrbit T t ∧
      (∀ e ∈ A, ∃ c ∈ C, ∃ x ∈ T, e = c * x) ∧
      (A : Set G) = (C : Set G) * (T : Set G) ∧
      C ⊓ T = ⊥ ∧ C.relIndex A = Nat.card T := by
  let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let A := D ⊓ Subgroup.centralizer ({u} : Set G)
  let T := L ⊓ D
  obtain ⟨hTA, htT, hdiff⟩ :=
    pair_hull_orbit_premises H a b t u ht hflip L hLC hLnormal htL
  have hfixed := odd_inverted_subgroup_trivial_centralizer T t hodd hinv
  obtain ⟨_, _, _, horbit, hfactor, hproduct, hinter, hindex⟩ :=
    odd_involution_orbit_product_index A T hTA t ht htT hfixed hdiff
  have hC := pair_first_centralizer_eq D u t
  have hidx :
      (D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)).relIndex A =
        (Subgroup.centralizer ({t} : Set G)).relIndex A := by
    rw [← hC]
    change ((A ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf A).index =
      ((Subgroup.centralizer ({t} : Set G)).subgroupOf A).index
    congr 1
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
  rw [hC] at hfactor hproduct hinter
  exact ⟨horbit, hfactor, hproduct, hinter, hidx.trans hindex⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
