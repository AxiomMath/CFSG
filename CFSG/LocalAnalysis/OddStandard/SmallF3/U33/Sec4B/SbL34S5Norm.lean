module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type*} [Group G]

theorem exists_zP (P V : Subgroup G) (hVc : ∀ p ∈ P, ∀ v ∈ V, p * v = v * p) :
    ∃ Z : Subgroup G, ∀ a : G, a ∈ Z ↔ a ∈ P ∧ ∀ q ∈ P, a * q * a⁻¹ * q⁻¹ ∈ V := by
  refine ⟨{ carrier := {a | a ∈ P ∧ ∀ q ∈ P, a * q * a⁻¹ * q⁻¹ ∈ V}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun a => Iff.rfl⟩
  · rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    refine ⟨P.mul_mem haP hbP, fun q hq => ?_⟩
    have hv : b * q * b⁻¹ * q⁻¹ ∈ V := hb q hq
    have hc : a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ = b * q * b⁻¹ * q⁻¹ := by
      rw [hVc a haP _ hv]; group
    rw [show a * b * q * (a * b)⁻¹ * q⁻¹
          = a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) by group, hc]
    exact V.mul_mem hv (ha q hq)
  · refine ⟨P.one_mem, fun q hq => ?_⟩
    rw [show (1 : G) * q * 1⁻¹ * q⁻¹ = 1 by group]
    exact V.one_mem
  · rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, fun q hq => ?_⟩
    have hv : (a * q * a⁻¹ * q⁻¹)⁻¹ ∈ V := V.inv_mem (ha q hq)
    have hc : a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a = (a * q * a⁻¹ * q⁻¹)⁻¹ := by
      rw [hVc a⁻¹ (P.inv_mem haP) _ hv]; group
    rw [show a⁻¹ * q * (a⁻¹)⁻¹ * q⁻¹
          = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a by group, hc]
    exact hv

theorem norm_trick_mem (O Q D V Z : Subgroup G) (ρ : G) (hρ3 : ρ * ρ * ρ = 1)
    (hQO : Q ≤ O) (hDO : D ≤ O) (hVQ : V ≤ Q) (hVZ : V ≤ Z)
    (hOc : ∀ a ∈ O, ∀ b ∈ O, a * b * a⁻¹ * b⁻¹ ∈ V) (hOs : ∀ a ∈ O, a * a ∈ V)
    (hVO : ∀ v ∈ V, ∀ a ∈ O, v * a = a * v)
    (hρQ : ∀ q ∈ Q, ρ * q * ρ⁻¹ ∈ Q) (hρD : ∀ d ∈ D, ρ * d = d * ρ)
    (hρZ : ∀ z ∈ Z, ρ * z * ρ⁻¹ ∈ Z)
    (hfix : ∀ q ∈ Q, ρ * q * ρ⁻¹ * q⁻¹ ∈ V → q ∈ V)
    {q d : G} (hq : q ∈ Q) (hd : d ∈ D) (hz : q * d ∈ Z) : d ∈ Z := by
  let q1 := ρ * q * ρ⁻¹
  let q2 := ρ * q1 * ρ⁻¹
  have hq1 : q1 = ρ * q * ρ⁻¹ := rfl
  have hq2 : q2 = ρ * q1 * ρ⁻¹ := rfl
  have hq1Q : q1 ∈ Q := hρQ q hq
  have hq2Q : q2 ∈ Q := hρQ q1 hq1Q
  have hqO : q ∈ O := hQO hq
  have hq1O : q1 ∈ O := hQO hq1Q
  have hq2O : q2 ∈ O := hQO hq2Q
  have hdO : d ∈ O := hDO hd
  have hq1q2O : q1 * q2 ∈ O := O.mul_mem hq1O hq2O
  have hρd : ρ * d * ρ⁻¹ = d := by rw [hρD d hd]; group
  have hρq2 : ρ * q2 * ρ⁻¹ = q := by
    rw [hq2, hq1]
    rw [show ρ * (ρ * (ρ * q * ρ⁻¹) * ρ⁻¹) * ρ⁻¹
          = (ρ * ρ * ρ) * q * (ρ * ρ * ρ)⁻¹ by group, hρ3]
    group
  have e1 : ρ * (q * d) * ρ⁻¹ = q1 * d := by
    rw [show ρ * (q * d) * ρ⁻¹ = (ρ * q * ρ⁻¹) * (ρ * d * ρ⁻¹) by group, hρd, ← hq1]
  have e2 : ρ * (ρ * (q * d) * ρ⁻¹) * ρ⁻¹ = q2 * d := by
    rw [e1, show ρ * (q1 * d) * ρ⁻¹ = (ρ * q1 * ρ⁻¹) * (ρ * d * ρ⁻¹) by group, hρd, ← hq2]
  have hconj : ρ * (q * q1 * q2) * ρ⁻¹ = q1 * q2 * q := by
    rw [show ρ * (q * q1 * q2) * ρ⁻¹
          = (ρ * q * ρ⁻¹) * (ρ * q1 * ρ⁻¹) * (ρ * q2 * ρ⁻¹) by group,
        ← hq1, ← hq2, hρq2]
  have hrV : q * q1 * q2 ∈ V :=
    hfix (q * q1 * q2) (Q.mul_mem (Q.mul_mem hq hq1Q) hq2Q) (by
      rw [hconj]
      rw [show q1 * q2 * q * (q * q1 * q2)⁻¹
            = (q1 * q2) * q * (q1 * q2)⁻¹ * q⁻¹ by group]
      exact hOc (q1 * q2) hq1q2O q hqO)
  let c := d * q1 * d⁻¹ * q1⁻¹
  have hc : c = d * q1 * d⁻¹ * q1⁻¹ := rfl
  have hcV : c ∈ V := hOc d hdO q1 hq1O
  have hddV : d * d ∈ V := hOs d hdO
  have hdq1 : d * q1 = c * q1 * d := by rw [hc]; group
  have hcq : q * c = c * q := (hVO c hcV q hqO).symm
  have hddq1 : q1 * (d * d) = (d * d) * q1 := (hVO (d * d) hddV q1 hq1O).symm
  have hddq : q * (d * d) = (d * d) * q := (hVO (d * d) hddV q hqO).symm
  let r := q * q1 * q2
  have hr : r = q * q1 * q2 := rfl
  have hmain : q * d * q1 * d * q2 = c * (d * d) * r := by
    rw [hr]
    calc q * d * q1 * d * q2
        = q * (d * q1) * d * q2 := by group
      _ = q * (c * q1 * d) * d * q2 := by rw [hdq1]
      _ = q * c * q1 * (d * d) * q2 := by group
      _ = c * q * q1 * (d * d) * q2 := by rw [hcq]
      _ = c * q * (q1 * (d * d)) * q2 := by group
      _ = c * q * ((d * d) * q1) * q2 := by rw [hddq1]
      _ = c * (q * (d * d)) * q1 * q2 := by group
      _ = c * ((d * d) * q) * q1 * q2 := by rw [hddq]
      _ = c * (d * d) * (q * q1 * q2) := by group
  let w := (q * d) * (ρ * (q * d) * ρ⁻¹) * (ρ * (ρ * (q * d) * ρ⁻¹) * ρ⁻¹)
  have hw : w = (q * d) * (ρ * (q * d) * ρ⁻¹) * (ρ * (ρ * (q * d) * ρ⁻¹) * ρ⁻¹) := rfl
  have hwZ : w ∈ Z := by
    rw [hw]
    have h1 : ρ * (q * d) * ρ⁻¹ ∈ Z := hρZ (q * d) hz
    have h2 : ρ * (ρ * (q * d) * ρ⁻¹) * ρ⁻¹ ∈ Z := hρZ _ h1
    exact Z.mul_mem (Z.mul_mem hz h1) h2
  have hwd : w * d⁻¹ ∈ V := by
    rw [hw]
    have hw_eq : (q * d) * (ρ * (q * d) * ρ⁻¹) * (ρ * (ρ * (q * d) * ρ⁻¹) * ρ⁻¹) * d⁻¹
               = q * d * q1 * d * q2 := by rw [e2, e1]; group
    rw [hw_eq, hmain]
    exact V.mul_mem (V.mul_mem hcV hddV) hrV
  have hd_eq : d = (w * d⁻¹)⁻¹ * w := by group
  rw [hd_eq]
  exact Z.mul_mem (Z.inv_mem (hVZ hwd)) hwZ

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
