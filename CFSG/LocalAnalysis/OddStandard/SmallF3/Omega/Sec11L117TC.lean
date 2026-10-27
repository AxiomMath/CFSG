module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem sec11_conj_eq_of_mem_zpowers {y z u : G} (hyz : y * z = z * y)
    (hu : u ∈ zpowers z) : y * u * y⁻¹ = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have h : y * z ^ k = z ^ k * y := ((show Commute y z from hyz).zpow_right k).eq
  rw [h]
  group

theorem sec11_comm_C_T {T C Q : Subgroup G} {a x z : G}
    (hgen : T = Subgroup.closure ((C : Set G) ∪ (Q : Set G) ∪ ({a, x} : Set G)))
    (hzc : ∀ g ∈ T, g * z = z * g)
    (hCel : ∀ c ∈ C, ∀ c' ∈ C, c * c' * c⁻¹ * c'⁻¹ ∈ zpowers z)
    (hQC : ∀ q ∈ Q, ∀ c ∈ C, q * c = c * q) (haC : ∀ c ∈ C, a * c = c * a)
    (hxC : ∀ c ∈ C, x * c * x⁻¹ * c⁻¹ ∈ zpowers z) :
    ∀ g ∈ T, ∀ c ∈ C, g * c * g⁻¹ * c⁻¹ ∈ zpowers z := by
  intro g hg
  rw [hgen] at hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    intro c hc
    rcases hy with (hy | hy) | hy
    · exact hCel y hy c hc
    · rw [hQC y hy c hc]
      simp
    · rcases hy with rfl | rfl
      · rw [haC c hc]
        simp
      · exact hxC c hc
  | one =>
    intro c hc
    simp
  | mul y y' hy hy' ihy ihy' =>
    intro c hc
    have hyz : y * z = z * y := hzc y (by rw [hgen]; exact hy)
    have hu := ihy' c hc
    have hv := ihy c hc
    have hyu : y * (y' * c * y'⁻¹ * c⁻¹) * y⁻¹ = y' * c * y'⁻¹ * c⁻¹ :=
      sec11_conj_eq_of_mem_zpowers hyz hu
    have hid : y * y' * c * (y * y')⁻¹ * c⁻¹ =
        (y * (y' * c * y'⁻¹ * c⁻¹) * y⁻¹) * (y * c * y⁻¹ * c⁻¹) := by group
    rw [hid, hyu]
    exact (zpowers z).mul_mem hu hv
  | inv y hy ihy =>
    intro c hc
    have hyz : y * z = z * y := hzc y (by rw [hgen]; exact hy)
    have hw := (zpowers z).inv_mem (ihy c hc)
    have hyw := sec11_conj_eq_of_mem_zpowers
      (((show Commute y z from hyz).inv_left).eq) hw
    have hid : y⁻¹ * c * y⁻¹⁻¹ * c⁻¹ = y⁻¹ * (y * c * y⁻¹ * c⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [hid, hyw]
    exact hw

end CFSG.OddStandard.SmallF3.Omega
