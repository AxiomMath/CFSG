module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped commutatorElement

variable {N : Type*} [Group N] {D : Subgroup N}

theorem commutatorElement_conj_right_of_commutator_le_centralizer [D.Normal]
    (hN : commutator N ≤ Subgroup.centralizer (D : Set N)) {d : N} (hd : d ∈ D) (x g : N) :
    ⁅d, g * x * g⁻¹⁆ = ⁅d, x⁆ := by
  have hdx : ⁅d, x⁆ ∈ D :=
    Subgroup.commutator_le_left D ⊤ (Subgroup.commutator_mem_commutator hd (Subgroup.mem_top x))
  have hcmem : ⁅g, x⁆ ∈ Subgroup.centralizer (D : Set N) :=
    hN (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x))
  rw [Subgroup.mem_centralizer_iff] at hcmem
  set c := ⁅g, x⁆ with hc
  have hd1 : d * c = c * d := hcmem d hd
  have hd2 : ⁅d, x⁆ * c = c * ⁅d, x⁆ := hcmem _ hdx
  have hgx : g * x * g⁻¹ = c * x := by rw [hc, commutatorElement_def]; group
  rw [hgx]
  calc ⁅d, c * x⁆ = c * ⁅d, x⁆ * c⁻¹ := by
        simp only [commutatorElement_def]
        calc d * (c * x) * d⁻¹ * (c * x)⁻¹
            = (d * c) * (x * d⁻¹ * x⁻¹ * c⁻¹) := by group
          _ = (c * d) * (x * d⁻¹ * x⁻¹ * c⁻¹) := by rw [hd1]
          _ = c * (d * x * d⁻¹ * x⁻¹) * c⁻¹ := by group
    _ = ⁅d, x⁆ := by rw [← hd2, mul_inv_cancel_right]

theorem normal_inf_centralizer_of_commutator_le_centralizer [D.Normal]
    (hN : commutator N ≤ Subgroup.centralizer (D : Set N)) (X : Subgroup N) :
    (D ⊓ Subgroup.centralizer (X : Set N)).Normal := by
  refine ⟨fun d hd g => ?_⟩
  rw [Subgroup.mem_inf] at hd ⊢
  obtain ⟨hdD, hdC⟩ := hd
  refine ⟨‹D.Normal›.conj_mem d hdD g, ?_⟩
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
  intro x hx
  have h0 : ⁅d, g⁻¹ * x * g⁻¹⁻¹⁆ = ⁅d, x⁆ :=
    commutatorElement_conj_right_of_commutator_le_centralizer hN hdD x g⁻¹
  rw [inv_inv] at h0
  have h1 : ⁅d, x⁆ = 1 := by
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one'] at hdC
    exact hdC x hx
  have h2 : ⁅g * d * g⁻¹, x⁆ = g * ⁅d, g⁻¹ * x * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h2, h0, h1, mul_one, mul_inv_cancel]

theorem normal_commutator_of_commutator_le_centralizer [D.Normal]
    (hN : commutator N ≤ Subgroup.centralizer (D : Set N)) (X : Subgroup N) :
    (⁅D, X⁆).Normal := by
  refine ⟨fun w hw g => ?_⟩
  have key : ⁅D, X⁆ ≤ (⁅D, X⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro d hd x hx
    have hd' : g * d * g⁻¹ ∈ D := ‹D.Normal›.conj_mem d hd g
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_commutatorElement]
    rw [commutatorElement_conj_right_of_commutator_le_centralizer hN hd' x g]
    exact Subgroup.commutator_mem_commutator hd' hx
  have h := key hw
  simpa using h

end CFSG.FeitThompson
