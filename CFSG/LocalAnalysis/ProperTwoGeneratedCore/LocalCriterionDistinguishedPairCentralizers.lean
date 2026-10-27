module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCentralizers

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem distinguished_odd_inverted_pair_full_centralizer_eq (H : Subgroup G)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (L : Subgroup G) (t : G) (ht : orderOf t = 2)
    (hthree : DistinguishedThreePointCentralization H
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) t)
    (hWodd : Odd (Nat.card (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G)))
    (hcomm : IsMulCommutative (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G))
    (hinv : ∀ x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b),
      rightConjugateElem x t = x⁻¹)
    (hCtwo : ∀ s : L, orderOf s = 2 → IsPGroup 2 (Subgroup.centralizer ({s} : Set L)))
    (x : G) (hxW : x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b))
    (hx : x ≠ 1) :
    elementFixedSet H x = {a, b} ∧
      L ⊓ Subgroup.centralizer ({x} : Set G) =
        L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) := by
  let W := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
  have hxodd : Odd (orderOf x) := by
    have h := hWodd.of_dvd_nat (orderOf_dvd_natCard (⟨x, hxW⟩ : W))
    exact (Subgroup.orderOf_coe (⟨x, hxW⟩ : W)) ▸ h
  have hfix := distinguished_pair_inverted_element_full_fixed_set H a b hab t ht hthree
    x hx hxW.2 hxodd (hinv x hxW)
  let y : L := ⟨x, hxW.1⟩
  have hyne : y ≠ 1 := by intro hy; exact hx (congrArg Subtype.val hy)
  have hyodd : Odd (orderOf y) := (Subgroup.orderOf_coe y).symm ▸ hxodd
  have hCodd : Odd (Nat.card (L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) :=
    (Nat.card_congr (internalCentralizerEquiv L x hxW.1).toEquiv).symm ▸
      odd_element_full_centralizer_odd y hyne hyodd hCtwo
  exact ⟨hfix, pair_full_centralizer_eq H a b hab L hcomm x hxW hfix hCodd⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
