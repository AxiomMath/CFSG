module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairNontrivial
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairLinearOrder
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinear

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem distinguished_original_linear_denominator
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
    {K : Type} [Field K] [Finite K] (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f)
    (e : L ≃* GLAProj (GLASLGroup (Fin 2) K))
    (phi : elementFixedSet H (u * t) ≃ ℙ K (Fin 2 → K))
    (hequiv : letI := productFixedSetAction H L (u * t) hLC
      letI := linearStandardAction K
      ∀ x : L, ∀ p : elementFixedSet H (u * t), phi (x • p) = e x • phi p) :
    let a := rightCosetMk H 1
    let D := H ⊓ rightCosetStabilizer H b
    let W := L ⊓ D
    let E := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    W ≠ ⊥ ∧ IsCyclic W ∧ Odd (Nat.card W) ∧
      (∀ x ∈ W, rightConjugateElem x t = x⁻¹) ∧
      (E : Set G) = (C : Set G) * (W : Set G) ∧ C ⊓ W = ⊥ ∧
      C.relIndex E = Nat.card W ∧
      (∀ x ∈ W, x ≠ 1 → elementFixedSet H x = {a, b} ∧
        L ⊓ Subgroup.centralizer ({x} : Set G) = W) ∧
      Nat.card W = Nat.card K + 1 := by
  let a := rightCosetMk H 1
  let D := H ⊓ rightCosetStabilizer H b
  let W := L ⊓ D
  have hbase : rightCosetStabilizer H a = H := rightCosetStabilizer_base H
  have huD' : u ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b := by
    rwa [hbase]
  have hgen' : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      distinguishedCommutator t
        ((oddCore (show Subgroup G from
          rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)).map
          (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b).subtype) = ⊤ := by
    rwa [hbase]
  have hthree' : DistinguishedThreePointCentralization H
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) t := by
    rwa [hbase]
  have hWne := distinguished_pair_hull_nontrivial_of_commutator_generation
    h a b hab t htclass hflip u hu hut huD' huz hunoncentral hgen' L hLC hLnormal htL
  rw [hbase] at hWne
  have hgeometry := distinguished_denominator_geometric_conclusions h a b hab t htclass
    hflip u hu hut huD' hthree' L hLC hLnormal htL hclass
    (linear_model_involution_centralizers_two f hf hcard e)
    (linear_model_oddSylow_cyclic f hf hcard e)
  dsimp only at hgeometry
  obtain ⟨hcyclic, hodd, _, hinv, hprod, hinter, hindex, hfull, _⟩ := hgeometry
  obtain ⟨x, hxW, hxne⟩ := (Subgroup.nontrivial_iff_exists_ne_one W).mp
    ((Subgroup.nontrivial_iff_ne_bot W).mpr hWne)
  have hxW' : x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) := by
    rwa [hbase]
  have horder := distinguished_linear_order_of_nonidentity h a b hab t htclass hflip
    u hu hut huD' hthree' L hLC hLnormal htL hclass f hf hcard e phi x hxW' hxne
  rw [hbase] at hcyclic hodd hinv hprod hinter hindex hfull horder
  have hsupplied_model := And.intro hoddCore hequiv
  clear hsupplied_model
  exact ⟨hWne, hcyclic, hodd, hinv, hprod, hinter, hindex, hfull, horder⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
