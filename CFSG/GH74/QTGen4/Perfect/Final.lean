module

public import CFSG.GH74.QTGen4.Perfect.ActsTrivially
public import CFSG.GH74.QTGen4.Perfect.Quasisimple
public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.QTGen4

theorem actsTriviallyStmt_holds : ActsTriviallyStmt :=
  fun hperf hQ hR φ => eq_one_of_perfect_of_card_dvd_20160 hperf hQ hR φ

theorem isQuasisimple_of_gorensteinWalter {Q : Type*} [Group Q]
    (h : CFSG.GorensteinWalter.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  obtain ⟨-, hperf, hsimple⟩ := h
  have : Group.IsPerfect Q := Group.isPerfect_def.2 hperf
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hsimple
  refine ⟨inferInstance, hsimple, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (G := Q ⧸ Subgroup.center Q) inferInstance

theorem isQuasisimple_of_perfect_card_dvd_20160 {Q : Type} [Group Q] [Finite Q] [Nontrivial Q]
    (hperf : commutator Q = ⊤) (hO2 : CFSG.pCore 2 Q = ⊥)
    (hsol : ∀ N : Subgroup Q, N.Normal → N ≠ ⊤ → Group.IsSolvable ↥N)
    (hcard : Nat.card Q ∣ 20160) : CFSG.IsQuasisimple Q :=
  isQuasisimple_of_gorensteinWalter
    (isQuasisimple_of_perfect_of_card_dvd_20160 actsTriviallyStmt_holds hperf hO2 hsol hcard)

end CFSG.GH74.QTGen4
