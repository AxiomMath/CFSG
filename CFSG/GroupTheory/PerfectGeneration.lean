module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PGroupQuotientOfPPrimeElements
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GroupTheory

theorem eq_top_of_isPerfect_of_forall_not_dvd_orderOf_mem {X : Type*} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) (hX : Group.IsPerfect X) {C : Subgroup X} [C.Normal]
    (hC : ∀ x : X, ¬ q ∣ orderOf x → x ∈ C) : C = ⊤ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Group.IsPerfect X := hX
  have hquot : IsPGroup q (X ⧸ C) :=
    CFSG.Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem C hC
  haveI : Group.IsNilpotent (X ⧸ C) := hquot.isNilpotent
  haveI : Group.IsSolvable (X ⧸ C) := inferInstance
  haveI : Group.IsPerfect (X ⧸ C) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
  have hsub : Subsingleton (X ⧸ C) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (X ⧸ C) inferInstance
  rw [eq_top_iff]
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

end CFSG.GroupTheory
