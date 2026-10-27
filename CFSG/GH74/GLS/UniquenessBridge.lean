module

public import CFSG.GH74.GLS.Types
public import CFSG.GH74.Uniqueness.Statements
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.GH74.GLS

open Subgroup

theorem pRank_subgroup_eq_open {G : Type*} [Group G] [Finite G] (p : ℕ) (Q : Subgroup G) :
    pRank p ↥Q = CFSG.Open.pRank p Q := CFSG.SectionRank.pRank_coe_eq_openPRank p Q

theorem gammaK_eq_properTwoGenCoreGamma {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    (k : ℕ) : gammaK 2 S k = CFSG.Open.properTwoGenCoreGamma S k := by
  simp only [gammaK, CFSG.Open.properTwoGenCoreGamma, pRank_subgroup_eq_open]

theorem gammaO_eq_gammaZero {G : Type*} [Group G] [Finite G] (S : Subgroup G) :
    gammaO 2 S = CFSG.GH74.Uniqueness.gammaZero S := by
  simp only [gammaO, CFSG.GH74.Uniqueness.gammaZero, pRank_subgroup_eq_open]

theorem isTwoUniquenessSubgroup_iff {G : Type*} [Group G] [Finite G] (M : Subgroup G) :
    IsTwoUniquenessSubgroup M ↔ CFSG.GH74.Uniqueness.IsTwoUniquenessSubgroup M := by
  simp only [IsTwoUniquenessSubgroup, CFSG.GH74.Uniqueness.IsTwoUniquenessSubgroup,
    pRank_subgroup_eq_open, gammaK_eq_properTwoGenCoreGamma, gammaO_eq_gammaZero]

end CFSG.GH74.GLS
