module

public import CFSG.LargeExtraspecial.S4Defs
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212G

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_M_eq_QG (S : Setting G) : pCoreOf 2 S.M = S.QG := by
  rw [pCoreOf, ← S.Q_eq_pCore]
  rfl

theorem isTypeJ4Core_of_card_QG_inf_Qa (S : Setting G) {g : G} (hw : S.width = 6)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hcard : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ 7) :
    Quasithin.H13.J4.IsTypeJ4Core S.M (Quasithin.H13.J4.selfC S.z) := by
  have hQc : Nat.card S.QG = 2 ^ (2 * 6 + 1) := by
    rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw]
  have hzA : S.z ∈ S.QG ⊓ S.Qa g := ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl haQ hne⟩
  have hcomm : ∀ x ∈ S.QG, ∀ y ∈ S.QG, ⁅x, y⁆ ∈ zpowers S.z := by
    intro x hx y hy
    rw [commutatorElement_def]
    rcases S.commutator_eq_one_or_z hx hy with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  have hsq : ∀ x ∈ S.QG, x ^ 2 ∈ zpowers S.z := by
    intro x hx
    rcases S.sq_eq_one_or_z hx with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  have hnc : ∀ a ∈ S.QG ⊓ S.Qa g, a ∉ zpowers S.z → ∃ x ∈ S.QG, ⁅a, x⁆ ≠ 1 := by
    intro a ha haz
    by_contra hcon
    push Not at hcon
    apply haz
    rcases S.eq_one_or_z_of_commute ha.1
      (fun y hy => commutatorElement_eq_one_iff_mul_comm.mp (hcon y hy)) with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  obtain ⟨hext, hcen, hiso⟩ := Quasithin.H13.extraspecial_d8_82 S.z_ne_one S.z_sq (e := 6)
    (by norm_num) hQc inf_le_left (fun a ha a' ha' => S.QG_inf_Qa_comm hne ha ha')
    (fun a ha => S.QG_inf_Qa_sq hne ha) hcard hzA (fun x hx => S.z_comm_QG hx) hcomm hsq hnc
  have hP := pCoreOf_M_eq_QG S
  refine Quasithin.H13.isTypeJ4Core_of_82 (C := S.M) (z := S.z) S.z_mem_M ?_ ?_ ?_ ?_ ?_
  · rw [hP]
    intro x hx
    exact S.mem_QG_of_commute hx.1 fun y hy => (mem_centralizer_iff.mp hx.2 y hy).symm
  · rw [hP]
    exact hext
  · rw [hP]
    exact hQc
  · rw [hP]
    exact hcen
  · rw [hP]
    exact hiso

theorem isTypeJ4Core_of_width_six (S : Setting G) (hw : S.width = 6) {g : G} (H : Hyp4 S g)
    (C : Cons311 S g) :
    Quasithin.H13.J4.IsTypeJ4Core S.M (Quasithin.H13.J4.selfC S.z) :=
  isTypeJ4Core_of_card_QG_inf_Qa S hw H.conj_mem H.conj_ne (by rw [C.card_QG_inf_Qa, hw])

end CFSG.GF2Type.Smith1979
