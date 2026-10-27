module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Basic
public import CFSG.GroupTheory.ElemAbelianClosure

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Off

theorem s0_relIndex_le_of_isMaxElemAbelian {G : Type} [Group G] [Finite G] {S A V : Subgroup G}
    (hA : Quasithin.IsMaxElemAbelian S A) (hV : IsElemAbelian 2 V) (hVS : V ≤ S) :
    (Subgroup.centralizer (A : Set G)).relIndex V ≤
      (Subgroup.centralizer (V : Set G)).relIndex A := by
  classical
  set C : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCA : C ≤ A := inf_le_left
  have hCel : IsElemAbelian 2 C := IsElemAbelian.mono hA.2.1 hCA
  have hcomm : ∀ x ∈ C, ∀ v ∈ V, x * v = v * x := fun x hx v hv =>
    (Subgroup.mem_centralizer_iff.1 hx.2 v hv).symm
  have hB := IsElemAbelian.sup_of_commute hCel hV hcomm
  have hcardB : Nat.card (C ⊔ V : Subgroup G) ≤ Nat.card A :=
    hA.2.2 _ (sup_le (hCA.trans hA.1) hVS) hB
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C V hcomm).1
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (V : Set G)) (K := A)
  have h2 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (A : Set G)) (K := V)
  rw [inf_comm] at h1
  rw [← hC] at h1
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hCVle : Nat.card (C ⊓ V : Subgroup G) ≤
      Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) := by
    apply Subgroup.card_le_of_le
    refine inf_le_inf ?_ le_rfl
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun a ha => hA.2.1.comm ha (hCA hx)
  set x := (Subgroup.centralizer (A : Set G)).relIndex V
  set y := (Subgroup.centralizer (V : Set G)).relIndex A
  have h3 : Nat.card C * Nat.card V ≤ y * Nat.card C * Nat.card (C ⊓ V : Subgroup G) := by
    rw [← hprod]
    calc Nat.card (C ⊔ V : Subgroup G) * Nat.card (C ⊓ V : Subgroup G)
        ≤ Nat.card A * Nat.card (C ⊓ V : Subgroup G) := Nat.mul_le_mul_right _ hcardB
      _ = y * Nat.card C * Nat.card (C ⊓ V : Subgroup G) := by rw [← h1]
  have h4 : Nat.card V ≤ y * Nat.card (C ⊓ V : Subgroup G) := by
    have : Nat.card C * Nat.card V ≤ Nat.card C * (y * Nat.card (C ⊓ V : Subgroup G)) := by
      calc Nat.card C * Nat.card V ≤ y * Nat.card C * Nat.card (C ⊓ V : Subgroup G) := h3
        _ = Nat.card C * (y * Nat.card (C ⊓ V : Subgroup G)) := by ring
    exact Nat.le_of_mul_le_mul_left this hCpos
  have hposW : 0 < Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) := Nat.card_pos
  have h5 : x * Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) ≤
      y * Nat.card (Subgroup.centralizer (A : Set G) ⊓ V : Subgroup G) := by
    rw [h2]
    exact h4.trans (Nat.mul_le_mul_left _ hCVle)
  exact Nat.le_of_mul_le_mul_right h5 hposW

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem s0_off_aux (h : Setup28 W K S) {A : Subgroup X} (hA : Quasithin.IsMaxElemAbelian S A) :
    (Subgroup.centralizer (A : Set X)).relIndex (vOf W K S) ≤ (kerAct W K S).relIndex A := by
  have h1 := s0_relIndex_le_of_isMaxElemAbelian hA (s0_v_props_aux h).1 (s0_vOf_le_S h)
  refine h1.trans (Subgroup.relIndex_le_of_le_left s0_kerAct_le_centralizer_V ?_)
  exact Subgroup.index_ne_zero_of_finite

end Off

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
