module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeSelection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem trivial_pair_intersection_centralizes_flip
    (H : Subgroup G) (a b : pointRightCosetSpace H)
    (t v : G) (ht : orderOf t = 2) (hflip : pointRightCosetMul H a t = b)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({v} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({v} : Set G))).Normal)
    (htL : t ∈ L)
    (hbot : L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) = ⊥) :
    (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) ⊓
      Subgroup.centralizer ({v} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨_, _, horbit⟩ := pair_hull_orbit_premises H a b t v ht hflip
    L hLC hLnormal htL
  intro e he
  have heq : rightConjugateElem t e * t = 1 :=
    Subgroup.mem_bot.mp (hbot ▸ horbit e he)
  have hright : rightConjugateElem t e = t := by
    have heqt := mul_eq_one_iff_eq_inv.mp heq
    rwa [inv_eq_self_of_orderOf_eq_two ht] at heqt
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  change e⁻¹ * t * e = t at hright
  have he' := congrArg (fun s : G => e * s) hright
  simpa only [mul_assoc, mul_inv_cancel_left] using he'.symm

theorem first_pair_commutator_centralizes (J : Subgroup G) (u t : G)
    (hut : Commute u t) :
    ⁅J ⊓ Subgroup.centralizer ({u} : Set G), Subgroup.zpowers t⁆ ≤
      Subgroup.centralizer ({u} : Set G) :=
  Subgroup.commutator_le_of_le inf_le_right
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hut.symm.eq))

theorem trivial_pair_intersection_commutator_factors
    (H : Subgroup G) (a b : pointRightCosetSpace H)
    (u t : G) (ht : orderOf t = 2) (hut : Commute u t)
    (hflip : pointRightCosetMul H a t = b)
    (J : Subgroup G) (hJD : J ≤ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L)
    (hbot : L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) = ⊥) :
    ⁅J ⊓ Subgroup.centralizer ({u} : Set G), Subgroup.zpowers t⁆ ≤
        Subgroup.centralizer ({u} : Set G) ∧
      ⁅J ⊓ Subgroup.centralizer ({u * t} : Set G), Subgroup.zpowers t⁆ = ⊥ := by
  refine ⟨first_pair_commutator_centralizes J u t hut, ?_⟩
  apply (commutator_zpowers_eq_bot_iff _ t).mpr
  intro j hj
  exact trivial_pair_intersection_centralizes_flip H a b t (u * t) ht hflip
    L hLC hLnormal htL hbot ⟨hJD hj.1, hj.2⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
