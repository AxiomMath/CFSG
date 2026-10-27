module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.A7Inputs
public meta import CFSG.GH74.KGroups.A7Inputs
public import Certificates.Certificate5109

public section

namespace CFSG.GH74.KGroups.A7

open CFSG.Certificates CFSG.Sporadic.Schreier

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 2520 :=
  Certificates.certificate5109.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 5040 :=
  Certificates.certificate5109.2.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem orders_ok :
    orderIs pa 2 = true ∧ orderIs pb 5 = true ∧ pairInvB ws pa pb = true :=
  Certificates.certificate5109.2.2.1

theorem count_ok_check : pairCountB QP 2 5 ws = 5040 :=
  Certificates.certificate5109.2.2.2.2.2.2

theorem count_ok : pairCountB QP 2 5 ws = QA.orderCertificate := by
  rw [QA_valid.2]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList pa pb = true :=
  Certificates.certificate5109.2.2.2.1

theorem cent_ok :
    centTrivCheck (elemsT QA) pa pb = true :=
  Certificates.certificate5109.2.2.2.2.1

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl | rfl <;> norm_num

theorem QP_eq_alt :
    QP.originalSubgroup = alternatingGroup (Fin 7) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [QP_closure, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]; decide
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]; decide
  · rw [card_group QP QP_ok, QP_valid.2, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]

theorem equiv_of_alt
    {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 7)) :
    Nonempty (K ≃* QP.originalSubgroup) :=
  ⟨e.trans (MulEquiv.subgroupCongr QP_eq_alt.symm)⟩

theorem autModel
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin 7)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  have ho := orders_ok
  exact autModel_exists QP QA QP_ok QA_ok pa pb QP_closure 2 5 (by norm_num) (by norm_num) ws
    ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1) ((orderIs_iff _ (by norm_num)).1 ho.2.1)
    ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok norm_ok cent_ok e

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem card_mulAut : Nat.card (MulAut K) = 5040 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  rw [M.card_mulAut, hA, card_group QA QA_ok, QA_valid.2]

end Consequences

end CFSG.GH74.KGroups.A7
