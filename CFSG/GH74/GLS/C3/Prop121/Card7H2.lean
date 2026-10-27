module

public import CFSG.GH74.GLS.C3.Prop121.Card7H1
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H1
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Prop121.Card7H2Inputs
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H2Inputs
public import Certificates.Certificate5080
public import Certificates.Certificate5081

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.HC

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

theorem ord3Check_true : ord3Check = true :=
  Certificates.certificate5081.1

theorem ord3_field
    (τ : H11) (h3 : τ ^ 3 = 1) (h1 : τ ≠ 1) :
    ((τ = tau1 ∨ τ = tau1⁻¹) ∧ ccard H11 τ τ = 576) ∨ ccard H11 τ τ ≤ 36 := by
  have h := of_decide_eq_true (List.all_eq_true.1 ord3Check_true (ev τ) (HL_complete τ))
  have h3' : ev τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have h1' : ev τ ≠ 1 := fun h => h1 (ev_injective (by rw [h, map_one]))
  have h2 := h h3' h1'
  rw [ccard_eq]
  have e1 : ev τ = T1 ↔ τ = tau1 := by
    rw [← ev_tau1]; exact ⟨fun h => ev_injective h, fun h => by rw [h]⟩
  have e2 : ev τ = T1⁻¹ ↔ τ = tau1⁻¹ := by
    rw [← ev_tau1, ← map_inv]; exact ⟨fun h => ev_injective h, fun h => by rw [h]⟩
  rw [e1, e2] at h2
  exact h2

theorem hp_b : Hp (swap 0 1 * swap 8 9) := by
  refine ⟨?_, ?_⟩
  · rw [sign_mul, sign_swap (by decide), sign_swap (by decide)]; rfl
  · unfold Y11; decide

theorem inv_tau1_field : ∃ b : H11, b * tau1 * b⁻¹ = tau1⁻¹ := by
  refine ⟨mkH _ hp_b, ev_injective ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, ev_mkH, ev_tau1]
  unfold T1
  decide

theorem centerCheck_true : centerCheck = true :=
  Certificates.certificate5081.2.1

theorem center_field
    (c : H11) (hc : ∀ h : H11, h * c = c * h) : c = 1 ∨ c = ystar := by
  have h := of_decide_eq_true (List.all_eq_true.1 centerCheck_true (ev c) (HL_complete c))
  have h2 : (HL.all fun h => decide (h * ev c = ev c * h)) = true := by
    rw [List.all_eq_true]
    intro h' hh'
    rw [decide_eq_true_iff]
    have := hc (mkH h' (HL_hp h' hh'))
    rw [ev_comm_iff, ev_mkH] at this
    exact this
  rcases h h2 with h3 | h3
  · left; exact ev_injective (by rw [h3, map_one])
  · right; exact ev_injective (by rw [h3, ev_ystar])

theorem ccL_T1_T1 : ccL T1 T1 = 576 :=
  Certificates.certificate5081.2.2.1

theorem card_B0_field :
    ccard H11 tau1 tau1 = 576 := by
  rw [ccard_eq, ev_tau1]; exact ccL_T1_T1

theorem B0invCheck_true : B0invCheck = true :=
  Certificates.certificate5081.2.2.2

theorem B0inv_field
    (b : H11) (hb : b * tau1 = tau1 * b) (hi : IsInv b) (hy : b ≠ ystar) :
    ccard H11 tau1 b = 48 ∨ ccard H11 tau1 b = 96 := by
  have h := of_decide_eq_true (List.all_eq_true.1 B0invCheck_true (ev b) (HL_complete b))
  rw [ev_isInv] at hi
  rw [ev_comm_iff, ev_tau1] at hb
  have hy' : ev b ≠ Y11 := fun h' => hy (ev_injective (by rw [h', ev_ystar]))
  rw [ccard_eq, ev_tau1]
  exact h hb hi.1 hi.2 hy'

end CFSG.GH74.GLS.C3.Prop121.Card7.HC
