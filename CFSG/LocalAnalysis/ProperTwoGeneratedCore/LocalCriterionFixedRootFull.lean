module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootFourGroup

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot

open CFSG
open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

attribute [local instance] Classical.propDecidable

theorem fixed_root_bot_card (H : Subgroup G) (z : G) :
    Nat.card {x : G // x ∈ conjugacyWithin H z ∧
      x ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G)} =
      Nat.card (conjugacyWithin H z) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun x => ?_
  constructor
  · exact fun hx => hx.1
  · intro hx
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have ha1 : a = 1 := ha
    subst a
    simp

theorem original_root_card_eq_t_centralizer_index [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) :
    Nat.card (conjugacyWithin H z) =
      (Subgroup.centralizer ({t} : Set G)).relIndex (pairOddCore H beta) := by
  have hbotC : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  have hindex := original_fixed_root_card_eq_centralizer_index h S hzS hzcenter hbeta ht
    W hWB hzW htW ⊥ bot_le
  rw [fixed_root_bot_card, ← centralizer_intersection_relative_index, hbotC, inf_top_eq] at hindex
  exact hindex

theorem original_fixed_root_four_group_cardinality_identity [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hcardW : Nat.card W = 4)
    (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) :
    let : Fintype W := Fintype.ofFinite W
    Nat.card (conjugacyWithin H z) *
        (Nat.card {x : G // x ∈ conjugacyWithin H z ∧
          x ∈ Subgroup.centralizer (W : Set G)}) ^ 2 =
      ∏ w ∈ Finset.univ.erase (1 : W),
        Nat.card {x : G // x ∈ conjugacyWithin H z ∧
          x ∈ Subgroup.centralizer (Subgroup.zpowers (w : G) : Set G)} := by
  classical
  let : Fintype W := Fintype.ofFinite W
  change Nat.card (conjugacyWithin H z) *
      (Nat.card {x : G // x ∈ conjugacyWithin H z ∧
        x ∈ Subgroup.centralizer (W : Set G)}) ^ 2 =
    ∏ w ∈ Finset.univ.erase (1 : W),
      Nat.card {x : G // x ∈ conjugacyWithin H z ∧
        x ∈ Subgroup.centralizer (Subgroup.zpowers (w : G) : Set G)}
  have hnormal := hWB.trans (original_pairOddCore_normalized h hbeta ht)
  have hindex := normalized_odd_four_group_relative_index_identity
    (pairOddCore H beta) W hcardW (pairOddCore_odd H beta) hnormal t htW
  have hm := original_root_card_eq_t_centralizer_index h S hzS hzcenter hbeta ht W hWB hzW htW
  have hwhole := original_fixed_root_card_eq_centralizer_index h S hzS hzcenter hbeta ht
    W hWB hzW htW W le_rfl
  rw [← centralizer_intersection_relative_index] at hwhole
  have heach (w : W) :
      Nat.card {x : G // x ∈ conjugacyWithin H z ∧
        x ∈ Subgroup.centralizer (Subgroup.zpowers (w : G) : Set G)} =
      (Subgroup.centralizer ({t} : Set G)).relIndex
        (pairOddCore H beta ⊓ Subgroup.centralizer ({(w : G)} : Set G)) := by
    have hwW : Subgroup.zpowers (w : G) ≤ W := Subgroup.zpowers_le.mpr w.property
    have hw := original_fixed_root_card_eq_centralizer_index h S hzS hzcenter hbeta ht
      W hWB hzW htW (Subgroup.zpowers (w : G)) hwW
    rw [← centralizer_intersection_relative_index, centralizer_zpowers_eq_singleton] at hw
    rw [centralizer_zpowers_eq_singleton]
    exact hw
  rw [hm, hwhole]
  calc
    _ = ∏ w ∈ Finset.univ.erase (1 : W),
        (Subgroup.centralizer ({t} : Set G)).relIndex
          (pairOddCore H beta ⊓ Subgroup.centralizer ({(w : G)} : Set G)) := hindex
    _ = _ := Finset.prod_congr rfl fun w _hw => (heach w).symm

theorem original_fixed_root_cardinality_identity_full [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hcardW : Nat.card W = 4)
    (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) :
    (∀ A : Subgroup G, A ≤ W →
      Nat.card {x : G // x ∈ conjugacyWithin H z ∧ x ∈ Subgroup.centralizer (A : Set G)} =
        (((pairOddCore H beta ⊓ Subgroup.centralizer (A : Set G)) ⊓
            Subgroup.centralizer ({t} : Set G)).subgroupOf
          (pairOddCore H beta ⊓ Subgroup.centralizer (A : Set G))).index) ∧
    (let : Fintype W := Fintype.ofFinite W;
      Nat.card (conjugacyWithin H z) *
          (Nat.card {x : G // x ∈ conjugacyWithin H z ∧
            x ∈ Subgroup.centralizer (W : Set G)}) ^ 2 =
        ∏ w ∈ Finset.univ.erase (1 : W),
          Nat.card {x : G // x ∈ conjugacyWithin H z ∧
            x ∈ Subgroup.centralizer (Subgroup.zpowers (w : G) : Set G)}) := by
  constructor
  · intro A hAW
    exact original_fixed_root_card_eq_centralizer_index h S hzS hzcenter hbeta ht
      W hWB hzW htW A hAW
  · exact original_fixed_root_four_group_cardinality_identity h S hzS hzcenter hbeta ht
      W hcardW hWB hzW htW

end CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
