module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairCentralizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem distinguished_denominator_geometric_conclusions
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H a t = b)
    (u : G) (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (hthree : DistinguishedThreePointCentralization H
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) t)
    (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L)
    (hclass : ∀ s ∈ L, orderOf s = 2 → s ∈ involutionPointClass z)
    (hCtwo : ∀ s : L, orderOf s = 2 →
      IsPGroup 2 (Subgroup.centralizer ({s} : Set L)))
    (hSylow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p L, IsCyclic P) :
    let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
    let W := L ⊓ D
    let E := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    IsCyclic W ∧ Odd (Nat.card W) ∧ IsMulCommutative W ∧
      (∀ x ∈ W, rightConjugateElem x t = x⁻¹) ∧
      (E : Set G) = (C : Set G) * (W : Set G) ∧ C ⊓ W = ⊥ ∧
      C.relIndex E = Nat.card W ∧
      (∀ x ∈ W, x ≠ 1 → elementFixedSet H x = {a, b} ∧
        L ⊓ Subgroup.centralizer ({x} : Set G) = W) ∧
      Disjoint (elementFixedSet H (u * t)) ({a, b} : Set (pointRightCosetSpace H)) := by
  let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let W := L ⊓ D
  let E := D ⊓ Subgroup.centralizer ({u * t} : Set G)
  let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
  have ht : orderOf t = 2 := order_two_of_mem_pointClass h.distinguished_order htclass
  have hodd := pair_hull_intersection_odd h a b hab L hclass
  have htLorder : orderOf (⟨t, htL⟩ : L) = 2 :=
    (Subgroup.orderOf_coe (⟨t, htL⟩ : L)).symm.trans ht
  have hfixed : W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ :=
    odd_pair_intersection_trivial_centralizer L W inf_le_left t htL hodd
      (hCtwo ⟨t, htL⟩ htLorder)
  obtain ⟨hWE, htW, horbit⟩ :=
    pair_hull_orbit_premises H a b t (u * t) ht hflip L hLC hLnormal htL
  obtain ⟨hWodd, hcomm, hinv, _, _, hprod, hinter, hindex⟩ :=
    odd_involution_orbit_product_index E W hWE t ht htW hfixed horbit
  have hCeq : E ⊓ Subgroup.centralizer ({t} : Set G) = C :=
    pair_second_centralizer_eq D u t ht
  have hcyclic := pair_hull_intersection_cyclic H a b t (u * t) ht hflip L
    hLC hLnormal htL hWodd (hCtwo ⟨t, htL⟩ htLorder) hSylow
  rw [hCeq] at hprod hinter
  have hindex' : C.relIndex E = Nat.card W := by
    rw [← hCeq, Subgroup.inf_relIndex_left]
    exact hindex
  refine ⟨hcyclic, hWodd, hcomm, hinv, hprod, hinter, hindex', ?_, ?_⟩
  · intro x hx hxne
    exact distinguished_odd_inverted_pair_full_centralizer_eq H a b hab L t ht hthree
      hWodd hcomm hinv hCtwo x hx hxne
  · exact (commuting_pair_product_geometry H a b hab u t hu ht hut huD hflip).2.2.2.2

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
