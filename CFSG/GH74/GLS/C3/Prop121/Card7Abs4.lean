module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs3

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem ystar_central (h : H11) : h * ystar = ystar * h := by
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.1 h.2

theorem cc3_le_cc3 {G : Type*} [Group G] [Finite G] (a u v : G) : cc3 a u v ≤ cc3 a u u := by
  unfold cc3
  refine Nat.card_le_card_of_injective (fun c => ⟨c.1, c.2.1, c.2.2.1, c.2.2.1⟩) ?_
  intro c d h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

theorem ccard_ystar_tau1 (hH : HFacts) : ccard H11 tau1 ystar = 576 := by
  rw [← hH.card_B0]
  unfold ccard
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun c => ?_))
  have := ystar_central c
  tauto

namespace Ctx

variable {G : Type} [Group G] [Finite G] {C : Ctx G}

@[expose] def Y1.psi (Y : C.Y1) (w : G) (hw : w * Y.y1 = Y.y1 * w) : H11 :=
  C.Ψh Y.h1 ⟨w, mem_centralizer_singleton_iff.2 hw⟩

omit [Finite G] in
theorem Y1.psi_y1 (hH : HFacts) (Y : C.Y1) : Y.psi Y.y1 rfl = ystar := by
  have hc : ∀ h : H11, h * Y.psi Y.y1 rfl = Y.psi Y.y1 rfl * h := by
    intro h
    obtain ⟨c, rfl⟩ := (C.Ψh Y.h1).surjective h
    unfold Y1.psi
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 c.2
  rcases hH.center _ hc with h1 | h1
  · exfalso
    have h2 : (⟨Y.y1, Y.mem_self⟩ : ↥(centralizer ({Y.y1} : Set G))) = 1 :=
      (C.Ψh Y.h1).injective (by rw [map_one]; exact h1)
    have h3 : Y.y1 = 1 := congrArg Subtype.val h2
    have := Y.orderOf_y1
    rw [h3, orderOf_one] at this
    omega
  · exact h1

theorem Y1.psi_comm_tau (hH : HFacts) (Y : C.Y1) {w : G} (hw : w * Y.y1 = Y.y1 * w)
    (hws : w * C.s = C.s * w) : Y.psi w hw * tau1 = tau1 * Y.psi w hw := by
  obtain ⟨hτ, -⟩ := Y.tau_cases hH
  have h1 : Y.psi w hw * C.Ψh Y.h1 ⟨C.s, Y.mem_cent_y1⟩ =
      C.Ψh Y.h1 ⟨C.s, Y.mem_cent_y1⟩ * Y.psi w hw := by
    unfold Y1.psi
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hws
  rcases hτ with h2 | h2
  · rw [h2] at h1; exact h1
  · rw [h2] at h1
    have := (Commute.inv_right_iff (a := Y.psi w hw) (b := tau1)).1 h1
    exact this

omit [Finite G] in
theorem Y1.psi_isInv (Y : C.Y1) {w : G} (hw : w * Y.y1 = Y.y1 * w) (hw2 : orderOf w = 2) :
    IsInv (Y.psi w hw) := by
  rw [isInv_iff_orderOf]
  unfold Y1.psi
  rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact hw2

theorem Y1.ccard_psi (hH : HFacts) (Y : C.Y1) {w : G} (hw : w * Y.y1 = Y.y1 * w) :
    ccard H11 tau1 (Y.psi w hw) = cc3 Y.y1 C.s w := by
  obtain ⟨hτ, -⟩ := Y.tau_cases hH
  have h := cc3_eq_ccard (a := Y.y1) (u := C.s) (v := w) (C.Ψh Y.h1) Y.mem_cent_y1
    (mem_centralizer_singleton_iff.2 hw)
  rw [h]
  unfold Y1.psi
  rcases hτ with h2 | h2
  · rw [h2]
  · rw [h2, ccard_inv_left]

theorem Y1.ge_48 (hH : HFacts) (Y : C.Y1) {w : G} (hw : w * Y.y1 = Y.y1 * w)
    (hws : w * C.s = C.s * w) (hw2 : orderOf w = 2) : 48 ≤ cc3 Y.y1 C.s w := by
  rw [← Y.ccard_psi hH hw]
  by_cases hy : Y.psi w hw = ystar
  · rw [hy, ccard_ystar_tau1 hH]; norm_num
  · rcases hH.B0inv _ (Y.psi_comm_tau hH hw hws) (Y.psi_isInv hw hw2) hy with h | h <;> omega

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
