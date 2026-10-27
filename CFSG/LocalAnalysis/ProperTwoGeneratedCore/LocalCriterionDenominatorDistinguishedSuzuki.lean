module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairNontrivial
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiFieldOvoid
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOrderTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open Matrix CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
open CFSG.BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem distinguished_original_suzuki_denominator
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hab : rightCosetMk H 1 ≠ b)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b)
    (u : G) (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ H ⊓ rightCosetStabilizer H b)
    (huz : Commute u z) (hunoncentral : u ∉ Subgroup.center G)
    (hthree : DistinguishedThreePointCentralization H (H ⊓ rightCosetStabilizer H b) t)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      distinguishedCommutator t
        ((oddCore (H ⊓ rightCosetStabilizer H b : Subgroup G)).map
          (H ⊓ rightCosetStabilizer H b).subtype) = ⊤)
    (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L)
    (hclass : ∀ s ∈ L, orderOf s = 2 → s ∈ involutionPointClass z)
    (hoddCore : oddCore L = ⊥)
    {K : Type} [Field K] [Finite K] (a : ℕ) (ha : 1 ≤ a)
    (hcard : Nat.card K = 2 ^ (2 * a + 1)) (e : L ≃* GLASzGroup a K)
    (phi : elementFixedSet H (u * t) ≃
      {p : ℙ K (Fin 4 → K) // p ∈ suppliedSuzukiOvoidSet a K})
    (hequiv : letI := productFixedSetAction H L (u * t) hLC
      ∀ x : L, ∀ p : elementFixedSet H (u * t),
        (phi (x • p) : ℙ K (Fin 4 → K)) =
          (GeneralLinearGroup.toLin (e x : GL (Fin 4) K)).toLinearEquiv •
            (phi p : ℙ K (Fin 4 → K))) :
    let alpha := rightCosetMk H 1
    let D := H ⊓ rightCosetStabilizer H b
    let W := L ⊓ D
    let E := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    W ≠ ⊥ ∧ IsCyclic W ∧ Odd (Nat.card W) ∧
      (∀ x ∈ W, rightConjugateElem x t = x⁻¹) ∧
      (E : Set G) = (C : Set G) * (W : Set G) ∧ C ⊓ W = ⊥ ∧
      C.relIndex E = Nat.card W ∧
      (∀ x ∈ W, x ≠ 1 → elementFixedSet H x = {alpha, b} ∧
        L ⊓ Subgroup.centralizer ({x} : Set G) = W) ∧
      (Nat.card W = Nat.card K - 2 ^ (a + 1) + 1 ∨
        Nat.card W = Nat.card K + 2 ^ (a + 1) + 1) := by
  let alpha := rightCosetMk H 1
  let D := H ⊓ rightCosetStabilizer H b
  let W := L ⊓ D
  have hbase : rightCosetStabilizer H alpha = H := rightCosetStabilizer_base H
  have huD' : u ∈ rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H b := by
    rwa [hbase]
  have hgen' : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      distinguishedCommutator t
        ((oddCore (show Subgroup G from
          rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H b)).map
          (rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H b).subtype) = ⊤ := by
    rwa [hbase]
  have hthree' : DistinguishedThreePointCentralization H
      (rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H b) t := by
    rwa [hbase]
  have hWne := distinguished_pair_hull_nontrivial_of_commutator_generation
    h alpha b hab t htclass hflip u hu hut huD' huz hunoncentral hgen' L hLC hLnormal htL
  rw [hbase] at hWne
  have hgeometry := distinguished_denominator_geometric_conclusions
    h alpha b hab t htclass hflip u hu hut huD' hthree' L hLC hLnormal htL hclass
    (suzuki_model_involution_centralizers_two a ha hcard e)
    (suzuki_model_oddSylow_cyclic a ha hcard e)
  dsimp only at hgeometry
  rw [hbase] at hgeometry
  obtain ⟨hWcyclic, hWodd, _, hinv, hprod, hinter, hindex, hfull, hdisjoint⟩ := hgeometry
  have hWC : W ≤ Subgroup.centralizer ({u * t} : Set G) := inf_le_left.trans hLC
  have hdiv := denominator_card_dvd_entire_fixedSet H W (u * t) hWC alpha b
    hdisjoint (fun x hx hne => (hfull x hx hne).1)
  have hdegree : Nat.card (elementFixedSet H (u * t)) = (Nat.card K) ^ 2 + 1 := by
    rw [Nat.card_congr phi]
    exact suppliedSuzukiOvoid_card a K
  rw [hdegree] at hdiv
  let U := W.subgroupOf L
  let eU : U ≃* W := Subgroup.subgroupOfEquivOfLe (show W ≤ L from inf_le_left)
  have hUcard : Nat.card U = Nat.card W := Nat.card_congr eU.toEquiv
  have hUne : U ≠ ⊥ := by
    intro hU
    apply hWne
    apply Subgroup.card_eq_one.mp
    rw [← hUcard, hU, Subgroup.card_bot]
  have hUcentralizer : ∀ x ∈ U, x ≠ 1 → Subgroup.centralizer ({x} : Set L) = U := by
    intro x hx hxne
    have hxW : (x : G) ∈ W := hx
    have hxGne : (x : G) ≠ 1 := fun h => hxne (Subtype.ext h)
    have hC : L ⊓ Subgroup.centralizer ({(x : G)} : Set G) = W :=
      (hfull (x : G) hxW hxGne).2
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff]
    change y * x = x * y ↔ (y : G) ∈ W
    rw [← hC]
    constructor
    · intro hy
      exact ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val hy)⟩
    · intro hy
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
  have horder := suzuki_actual_full_centralizer_card a ha hcard e U hUne
    (hUcard.symm ▸ hdiv) hUcentralizer
  rw [hUcard] at horder
  have hsupplied_model := And.intro hoddCore hequiv
  clear hsupplied_model
  exact ⟨hWne, hWcyclic, hWodd, hinv, hprod, hinter, hindex, hfull, horder⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
