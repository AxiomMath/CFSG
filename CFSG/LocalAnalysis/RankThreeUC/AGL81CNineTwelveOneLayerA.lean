module

public import CFSG.Foundations.Basic

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftA
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

theorem normal_map_of_isComponent {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    {X : Subgroup Y} [X.Normal] (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r X ≤ 3)
    {J : Subgroup ↥X} (hJ : CFSG.IsComponent J) : (J.map X.subtype).Normal := by
  have hJ' : CFSG.Open.IsComponentOf (J.map X.subtype) X := by
    refine ⟨Subgroup.map_subtype_le J, ?_, ?_⟩
    · have h1 := (CFSG.Open.IsSubnormal.of_mathlib hJ.2).map X.subtype
      rwa [Subgroup.map_top, Subgroup.range_subtype] at h1
    · have hqJ : CFSG.Open.IsQuasisimple J := ⟨hJ.1.1.commutator_eq_top, hJ.1.2.1⟩
      exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (J.equivMapOfInjective X.subtype X.subtype_injective).symm hqJ
  have hnorm := CFSG.LocalAnalysis.RankThreeUC.S15.perfect_le_normalizer_component_gen
    X hrk ⊤ Subgroup.commutator_eq_self (J.map X.subtype) hJ'
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
