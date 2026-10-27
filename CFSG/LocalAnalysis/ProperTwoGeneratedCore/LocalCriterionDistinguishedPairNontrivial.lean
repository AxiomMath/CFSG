module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairCommutator
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairGeneration

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

variable {G : Type*} [Group G] [Finite G]

theorem distinguished_pair_hull_nontrivial_of_commutator_generation
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H a t = b)
    (u : G) (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (huz : Commute u z) (hunoncentral : u ∉ Subgroup.center G)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      distinguishedCommutator t
        ((oddCore (show Subgroup G from
          rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)).map
          (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b).subtype) = ⊤)
    (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L) :
    L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) ≠ ⊥ := by
  let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let J := (oddCore D).map D.subtype
  obtain ⟨hne, ht, _, _, hJD, hJodd, hVN⟩ :=
    distinguished_pair_odd_core_four_group_inputs h a b hab t htclass hflip u hu hut huD
  intro hbot
  have huN : u ∈ Subgroup.normalizer (J : Set G) :=
    hVN (Subgroup.subset_closure (by simp))
  have htN : t ∈ Subgroup.normalizer (J : Set G) :=
    hVN (Subgroup.subset_closure (by simp))
  have hcut : J ⊓ Subgroup.centralizer ({u * t} : Set G) ≤
      Subgroup.centralizer ({t} : Set G) := by
    intro j hj
    exact trivial_pair_intersection_centralizes_flip H a b t (u * t) ht hflip
      L hLC hLnormal htL hbot ⟨hJD hj.1, hj.2⟩
  have hcomm : ⁅J, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer ({u} : Set G) :=
    odd_four_group_commutator_centralized J u t hu ht hne hut huN htN hJodd hcut
  exact hunoncentral (center_of_distinguished_commutator_generation
    z t u ht huz hut J hgen hcomm)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
