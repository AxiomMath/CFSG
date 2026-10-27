module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFreeAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinearInvolutions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinearOrder

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization

variable {G : Type*} [Group G] [Finite G]

theorem distinguished_linear_order_of_nonidentity
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
    {K : Type} [Field K] [Finite K] (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f)
    (e : L ≃* GLAProj (GLASLGroup (Fin 2) K))
    (phi : elementFixedSet H (u * t) ≃ ℙ K (Fin 2 → K))
    (x : G)
    (hxW : x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b))
    (hxne : x ≠ 1) :
    Nat.card (L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G) =
      Nat.card K + 1 := by
  let W := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
  have hcore := distinguished_denominator_geometric_conclusions h a b hab t htclass hflip
    u hu hut huD hthree L hLC hLnormal htL hclass
    (linear_model_involution_centralizers_two f hf hcard e)
    (linear_model_oddSylow_cyclic f hf hcard e)
  dsimp only at hcore
  obtain ⟨_, hWodd, _, _, _, _, _, hfull, hdisjoint⟩ := hcore
  have hWC : W ≤ Subgroup.centralizer ({u * t} : Set G) := inf_le_left.trans hLC
  have hdiv := denominator_card_dvd_entire_fixedSet H W (u * t) hWC a b
    hdisjoint (fun y hy hne => (hfull y hy hne).1)
  have hdegree : Nat.card (elementFixedSet H (u * t)) = Nat.card K + 1 := by
    rw [Nat.card_congr phi]
    exact Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp)
  rw [hdegree] at hdiv
  let U := W.subgroupOf L
  let eU : U ≃* W := Subgroup.subgroupOfEquivOfLe (show W ≤ L from inf_le_left)
  have hUcard : Nat.card U = Nat.card W := Nat.card_congr eU.toEquiv
  have hUne : U ≠ ⊥ := by
    intro hU
    have hxU : (⟨x, hxW.1⟩ : L) ∈ U := hxW
    have hxone : (⟨x, hxW.1⟩ : L) = 1 := Subgroup.mem_bot.mp (hU ▸ hxU)
    exact hxne (congrArg Subtype.val hxone)
  have hUcentralizer : ∀ y ∈ U, y ≠ 1 → Subgroup.centralizer ({y} : Set L) = U := by
    intro y hy hyne
    have hyW : (y : G) ∈ W := hy
    have hyGne : (y : G) ≠ 1 := fun h => hyne (Subtype.ext h)
    have hC : L ⊓ Subgroup.centralizer ({(y : G)} : Set G) = W :=
      (hfull (y : G) hyW hyGne).2
    ext w
    rw [Subgroup.mem_centralizer_singleton_iff]
    change w * y = y * w ↔ (w : G) ∈ W
    rw [← hC]
    constructor
    · intro hw
      exact ⟨w.property, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val hw)⟩
    · intro hw
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hw.2)
  have horder := linear_actual_full_centralizer_card f hf hcard e U hUne
    (hUcard.symm ▸ hWodd) (hUcard.symm ▸ hdiv) hUcentralizer
  rwa [hUcard] at horder

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
