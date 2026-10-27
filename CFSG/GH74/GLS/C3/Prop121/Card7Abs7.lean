module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs1

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem card_transport_subtype {G B : Type*} [Group G] [Group B] {a : G}
    (e : ↥(centralizer ({a} : Set G)) ≃* B) (P : G → Prop) (Q : B → Prop)
    (hmem : ∀ g, P g → g ∈ centralizer ({a} : Set G))
    (hPQ : ∀ d : ↥(centralizer ({a} : Set G)), P (d : G) ↔ Q (e d)) :
    Nat.card {g : G // P g} = Nat.card {b : B // Q b} := by
  refine Nat.card_congr
    { toFun := fun g => ⟨e ⟨g.1, hmem g.1 g.2⟩, (hPQ ⟨g.1, hmem g.1 g.2⟩).1 g.2⟩
      invFun := fun b => ⟨((e.symm b.1 : ↥(centralizer ({a} : Set G))) : G),
        (hPQ (e.symm b.1)).2 (by simpa using b.2)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro g; ext; simp
  · intro b; ext; simp

namespace Ctx

variable {G : Type} [Group G] {C : Ctx G}

theorem orderOf_iota (d : ↥(centralizer ({C.x} : Set G))) :
    orderOf (C.ι d) = orderOf (d : G) := by
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]

theorem XF_iff (d : ↥(centralizer ({C.x} : Set G))) :
    XF (C.ι d) ↔ (orderOf (d : G) = 2 ∧ IsConj C.x (d : G)) := by
  constructor
  · rintro ⟨hi, h4⟩
    have h2 : orderOf (d : G) = 2 := by rw [← orderOf_iota, ← isInv_iff_orderOf]; exact hi
    have h2' : orderOf d = 2 := by rw [← Subgroup.orderOf_coe]; exact h2
    exact ⟨h2, isConj_comm.1 ((C.lab d h2').2 h4)⟩
  · rintro ⟨h2, hc⟩
    have h2' : orderOf d = 2 := by rw [← Subgroup.orderOf_coe]; exact h2
    refine ⟨?_, (C.lab d h2').1 (isConj_comm.1 hc)⟩
    rw [isInv_iff_orderOf, orderOf_iota]; exact h2

theorem YF_iff (hF : FFacts) (d : ↥(centralizer ({C.x} : Set G))) :
    YF (C.ι d) ↔ (orderOf (d : G) = 2 ∧ ¬ IsConj C.x (d : G)) := by
  constructor
  · rintro ⟨hi, h8⟩
    have h2 : orderOf (d : G) = 2 := by rw [← orderOf_iota, ← isInv_iff_orderOf]; exact hi
    have h2' : orderOf d = 2 := by rw [← Subgroup.orderOf_coe]; exact h2
    refine ⟨h2, fun hc => ?_⟩
    have := (C.lab d h2').1 (isConj_comm.1 hc)
    omega
  · rintro ⟨h2, hc⟩
    have h2' : orderOf d = 2 := by rw [← Subgroup.orderOf_coe]; exact h2
    have hi : IsInv (C.ι d) := by rw [isInv_iff_orderOf, orderOf_iota]; exact h2
    refine ⟨hi, ?_⟩
    rcases hF.inv_nm _ hi with h4 | h8
    · exact absurd (isConj_comm.1 ((C.lab d h2').2 h4)) hc
    · exact h8

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
