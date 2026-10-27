module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

open CFSG.ClassicalInvolution.Balance

section U16

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem enum8 {Y : Type} [Group Y] (a b c : Y) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    ∀ x ∈ Subgroup.closure ({a, b, c} : Set Y),
      x = 1 ∨ x = a ∨ x = b ∨ x = c ∨ x = a * b ∨ x = a * c ∨ x = b * c ∨ x = a * b * c := by
  have hba : b * a = a * b := hab.symm
  have hca : c * a = a * c := hac.symm
  have hcb : c * b = b * c := hbc.symm
  have hba' : ∀ r : Y, b * (a * r) = a * (b * r) := fun r => by rw [← mul_assoc, hba, mul_assoc]
  have hca' : ∀ r : Y, c * (a * r) = a * (c * r) := fun r => by rw [← mul_assoc, hca, mul_assoc]
  have hcb' : ∀ r : Y, c * (b * r) = b * (c * r) := fun r => by rw [← mul_assoc, hcb, mul_assoc]
  have ha' : ∀ r : Y, a * (a * r) = r := fun r => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ r : Y, b * (b * r) = r := fun r => by rw [← mul_assoc, hb, one_mul]
  have hc' : ∀ r : Y, c * (c * r) = r := fun r => by rw [← mul_assoc, hc, one_mul]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact Or.inl rfl
  | mul_right x hx y hy ihx =>
    rcases hy with rfl | rfl | rfl
    all_goals
      rcases ihx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [mul_assoc, hba, hca, hcb, hba', hca', hcb', ha', hb', hc', ha, hb, hc]
  | mul_inv_cancel x hx y hy ihx =>
    rcases hy with rfl | rfl | rfl
    all_goals
      rcases ihx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [mul_assoc, hba, hca, hcb, hba', hca', hcb', ha', hb', hc', ha, hb, hc, hai, hbi, hci]

theorem geg_eq (hc : P23Cfg n Y R S t K' W u e g) : g * e * g⁻¹ = e := by
  have hd := hc.data
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  rw [T7K.comm_e hd hgN]
  group

theorem g_mem_normalizer_B (hc : P23Cfg n Y R S t K' W u e g) :
    g ∈ Subgroup.normalizer ((Subgroup.closure ({u * e, u, t} : Set Y) : Subgroup Y) : Set Y) := by
  set B := Subgroup.closure ({u * e, u, t} : Set Y) with hBdef
  have hd := hc.data
  have hguB := gug_mem_B hc
  have hueB : u * e ∈ B := Subgroup.subset_closure (by simp)
  have hgt : g * t * g⁻¹ = u * e := hd.hgt
  have hge := geg_eq hc
  have hle : B ≤ B.comap (MulAut.conj g).toMonoidHom := by
    rw [hBdef, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h | h
    · rw [h]
      show g * (u * e) * g⁻¹ ∈ B
      have : g * (u * e) * g⁻¹ = (g * u * g⁻¹) * (g * e * g⁻¹) := by group
      rw [this, hge]
      exact Subgroup.mul_mem _ hguB (by
        have : e = u⁻¹ * (u * e) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))) hueB)
    · rw [h]; exact hguB
    · rw [h]
      show g * t * g⁻¹ ∈ B
      rw [hgt]; exact hueB
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  exact hle hx

end U16

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
