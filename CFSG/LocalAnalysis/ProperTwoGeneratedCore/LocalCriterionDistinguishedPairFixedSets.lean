module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

@[expose] def DistinguishedThreePointCentralization (H D : Subgroup G) (t : G) : Prop :=
  ∀ X : Subgroup G, X ≤ D → 3 ≤ Nat.card (pointFixedSet H X) →
    t ∈ Subgroup.normalizer (X : Set G) → X ≤ Subgroup.centralizer ({t} : Set G)

theorem distinguished_pair_inverted_element_full_fixed_set [Finite G]
    (H : Subgroup G) (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (t : G) (ht : orderOf t = 2)
    (hthree : DistinguishedThreePointCentralization H
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) t)
    (x : G) (hx : x ≠ 1)
    (hxD : x ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (hodd : Odd (orderOf x)) (hinv : rightConjugateElem x t = x⁻¹) :
    elementFixedSet H x = {a, b} := by
  have hxcyclic : Subgroup.zpowers x ≤
      rightCosetStabilizer H a ⊓ rightCosetStabilizer H b :=
    Subgroup.zpowers_le.mpr hxD
  have ha : a ∈ pointFixedSet H (Subgroup.zpowers x) :=
    (mem_pointFixedSet_iff H _ a).mpr (hxcyclic.trans inf_le_left)
  have hb : b ∈ pointFixedSet H (Subgroup.zpowers x) :=
    (mem_pointFixedSet_iff H _ b).mpr (hxcyclic.trans inf_le_right)
  ext c
  constructor
  · intro hc
    by_contra hnot
    have hca : c ≠ a := by intro heq; exact hnot (by simp [heq])
    have hcb : c ≠ b := by intro heq; exact hnot (by simp [heq])
    have hcard := right_fixed_triple_card H (Subgroup.zpowers x) a b c hab hca hcb
      ha hb ((pointFixedSet_zpowers_eq H x).symm ▸ hc)
    have hcentral := hthree _ hxcyclic hcard (inverter_normalizes_zpowers x t ht hinv)
    exact odd_inverted_element_not_commute x t hx hodd hinv
      (Subgroup.mem_centralizer_singleton_iff.mp (hcentral (Subgroup.mem_zpowers x)))
  · intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact (pointFixedSet_zpowers_eq H x) ▸ ha
    · exact (pointFixedSet_zpowers_eq H x) ▸ hb

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
