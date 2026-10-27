module

public import CFSG.GH74.E2.ComponentsFacts
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.GH74.KGroups.CoverL34
public import CFSG.GH74.KGroups.TwoM12Cover
public import CFSG.GH74.KGroups.CoverM11
public import CFSG.GH74.KGroups.M22
public import CFSG.GH74.KGroups.CoverJ2
public import CFSG.GH74.KGroups.CoverM23
public import CFSG.GH74.KGroups.CoverJ3

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint CFSG.GH74

theorem e2ComponentFacts_of_sz8
    (hsz : ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) → LieModel (K
        ⧸ center K) .twistedB2 0 2 3 → Nat.card (center K) ≤ 2 ∨ ¬ Gen4 K) : E2ComponentFacts where
  noTwoCover_even := fun S _ h => KGroups.noTwoCover_even S h
  l34_cover := KGroups.L34.l34_cover
  sz8_cover := hsz
  m12_cover := by
    intro K _ _ hq hZ hM
    exact KGroups.TwoM12.m12_cover_of_standard K hq hZ hM
  noTwoCover_sporadic := fun S _ h => KGroups.M11.noTwoCover_M11 S h
  cover_not_gen4 := by
    intro K _ _ hK hZ2 h hZ
    rcases h with h | h
    · exact KGroups.M22.cover_not_gen4_M22 K hK hZ2 h hZ
    · exact KGroups.J2.cover_not_gen4_J2 K hK hZ2 h hZ
  cover_not_gen4_M23_J3 := by
    intro K _ _ hK hZ2 h hZ
    rcases h with h | h
    · exact KGroups.M23.cover_not_gen4_M23 K hK hZ2 h hZ
    · exact KGroups.J3.cover_not_gen4_J3 K hK hZ2 h hZ

end CFSG.GH74.E2
