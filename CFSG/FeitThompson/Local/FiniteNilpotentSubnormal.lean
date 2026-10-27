module

public import Mathlib.GroupTheory.IsSubnormal
public import CFSG.FeitThompson.Foundations.NilpotentNormalizerCondition

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem isSubnormal_of_normalizerCondition [WellFoundedGT (Subgroup G)]
    (hnc : NormalizerCondition G) (H : Subgroup G) : H.IsSubnormal := by
  induction H using WellFoundedGT.induction with
  | _ H ih =>
    rcases eq_or_lt_of_le (le_top (a := H)) with rfl | hH
    · exact Subgroup.IsSubnormal.top
    · exact Subgroup.IsSubnormal.step H (normalizer (H : Set G)) le_normalizer
        (ih _ (hnc H hH)) Subgroup.normal_in_normalizer

theorem isSubnormal_of_finite_of_isNilpotent [Finite G] [Group.IsNilpotent G] (T : Subgroup G) :
    T.IsSubnormal :=
  isSubnormal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent T

theorem IsCentralSeries.isSubnormal [Finite G] {X : ℕ → Subgroup G} {r : ℕ}
    (hX : IsCentralSeries X r) (T : Subgroup G) : T.IsSubnormal :=
  isSubnormal_of_normalizerCondition (fun _ hH => hX.lt_normalizer hH) T

theorem exists_subnormal_chain_of_finite_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    (T : Subgroup G) : ∃ (m : ℕ) (C : ℕ → Subgroup G), C 0 = T ∧ C m = ⊤ ∧ Monotone C ∧
      ∀ i, ((C i).subgroupOf (C (i + 1))).Normal := by
  obtain ⟨m, C, hmono, hnormal, h0, hm⟩ :=
    Subgroup.IsSubnormal.isSubnormal_iff.mp (isSubnormal_of_finite_of_isNilpotent T)
  exact ⟨m, C, h0, hm, hmono, hnormal⟩

end

end CFSG.FeitThompson
