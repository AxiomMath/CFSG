module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type*} [Group G]

theorem conj_act_eq (V : Subgroup G) (B : Set G) (p t : G) (hVsq : ∀ v ∈ V, v * v = 1)
    (hpV : ∀ v ∈ V, p * v = v * p) (htV : ∀ v ∈ V, t * v = v * t)
    (hpB : ∀ b ∈ B, b * p * b⁻¹ * p⁻¹ ∈ V) (htB : ∀ b ∈ B, t * b * t⁻¹ * b⁻¹ ∈ V) :
    ∀ b ∈ B, (p * t * p⁻¹) * b * (p * t * p⁻¹)⁻¹ = t * b * t⁻¹ := by
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have hx2 : x * x = 1 := hVsq x hx
    have hy2 : y * y = 1 := hVsq y hy
    have hxy2 : (x * y) * (x * y) = 1 := hVsq (x * y) (V.mul_mem hx hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy2).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
        rw [inv_eq_of_mul_eq_one_right hx2, inv_eq_of_mul_eq_one_right hy2]
  intro b hb
  set c : G := b * p * b⁻¹ * p⁻¹ with hcdef
  set e : G := t * b * t⁻¹ * b⁻¹ with hedef
  have hcV : c ∈ V := by rw [hcdef]; exact hpB b hb
  have heV : e ∈ V := by rw [hedef]; exact htB b hb
  have hceV : c * e ∈ V := V.mul_mem hcV heV
  have hc2 : c * c = 1 := hVsq c hcV
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hpc : p * c = c * p := hpV c hcV
  have hpe : p * e = e * p := hpV e heV
  have hpc_e : p * (c * e) = (c * e) * p := hpV (c * e) hceV
  have htc : t * c = c * t := htV c hcV
  have hte : t * e = e * t := htV e heV
  have hce : c * e = e * c := hVcomm c hcV e heV
  have hcpb : c * (p * b) = b * p := by rw [hcdef]; group
  have htconj : t * b * t⁻¹ = e * b := by rw [hedef]; group
  have hp_inv_c : p⁻¹ * c * p = c := by
    calc p⁻¹ * c * p = p⁻¹ * (c * p) := by group
      _ = p⁻¹ * (p * c) := by rw [← hpc]
      _ = c := by group
  have hpinv : p⁻¹ * b * p = c * b := by
    calc p⁻¹ * b * p = p⁻¹ * (b * p) := by group
      _ = p⁻¹ * (c * (p * b)) := by rw [← hcpb]
      _ = (p⁻¹ * c * p) * b := by group
      _ = c * b := by rw [hp_inv_c]
  have hpconj : p * b * p⁻¹ = c * b := by
    have hb_eq : b = c * (p * b * p⁻¹) := by
      calc b = p * (p⁻¹ * b * p) * p⁻¹ := by group
        _ = p * (c * b) * p⁻¹ := by rw [hpinv]
        _ = c * (p * b * p⁻¹) := by
              rw [show p * (c * b) * p⁻¹ = (p * c) * b * p⁻¹ by group, hpc]
              group
    calc p * b * p⁻¹ = c⁻¹ * (c * (p * b * p⁻¹)) := by group
      _ = c⁻¹ * b := by rw [← hb_eq]
      _ = c * b := by rw [hc_inv]
  have htcb : t * (c * b) * t⁻¹ = c * (t * b * t⁻¹) := by
    calc t * (c * b) * t⁻¹ = (t * c) * b * t⁻¹ := by group
      _ = (c * t) * b * t⁻¹ := by rw [htc]
      _ = c * (t * b * t⁻¹) := by group
  have hfin : (c * e) * (c * b) = e * b := by
    calc (c * e) * (c * b) = c * (e * c) * b := by group
      _ = c * (c * e) * b := by rw [← hce]
      _ = e * b := by rw [← mul_assoc, hc2]; group
  calc (p * t * p⁻¹) * b * (p * t * p⁻¹)⁻¹
      = p * (t * (p⁻¹ * b * p) * t⁻¹) * p⁻¹ := by group
    _ = p * (t * (c * b) * t⁻¹) * p⁻¹ := by rw [hpinv]
    _ = p * (c * (t * b * t⁻¹)) * p⁻¹ := by rw [htcb]
    _ = p * (c * (e * b)) * p⁻¹ := by rw [htconj]
    _ = (c * e) * (p * b * p⁻¹) := by
          rw [show p * (c * (e * b)) * p⁻¹ = (p * (c * e)) * b * p⁻¹ by group, hpc_e]
          group
    _ = (c * e) * (c * b) := by rw [hpconj]
    _ = e * b := hfin
    _ = t * b * t⁻¹ := by rw [← htconj]

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
