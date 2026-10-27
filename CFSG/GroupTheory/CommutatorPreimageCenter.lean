module

public import Mathlib.GroupTheory.Commutator.Basic

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_subgroup_mem_iff_commutator_mem {R P : Subgroup G}
    (hPR : P ≤ normalizer (R : Set G)) :
    ∃ D : Subgroup G, ∀ x : G, x ∈ D ↔ x ∈ P ∧ ∀ p ∈ P, ⁅x, p⁆ ∈ R := by
  refine ⟨{ carrier := {x | x ∈ P ∧ ∀ p ∈ P, ⁅x, p⁆ ∈ R}
            one_mem' := ⟨P.one_mem, fun p _ => by
              rw [commutatorElement_one_left]; exact R.one_mem⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun _ => Iff.rfl⟩
  · rintro x y ⟨hxP, hx⟩ ⟨hyP, hy⟩
    refine ⟨P.mul_mem hxP hyP, fun p hp => ?_⟩
    have h1 : x * ⁅y, p⁆ * x⁻¹ ∈ R :=
      (mem_normalizer_iff.mp (hPR hxP) ⁅y, p⁆).mp (hy p hp)
    rw [show ⁅x * y, p⁆ = x * ⁅y, p⁆ * x⁻¹ * ⁅x, p⁆ by
      simp only [commutatorElement_def]; group]
    exact R.mul_mem h1 (hx p hp)
  · rintro x ⟨hxP, hx⟩
    refine ⟨P.inv_mem hxP, fun p hp => ?_⟩
    rw [show ⁅x⁻¹, p⁆ = x⁻¹ * ⁅x, p⁆⁻¹ * x by
      simp only [commutatorElement_def]; group]
    exact (mem_normalizer_iff''.mp (hPR hxP) ⁅x, p⁆⁻¹).mp (R.inv_mem (hx p hp))

theorem sup_inf_sup_le_of_commutator_le {D R M N : Subgroup G}
    (hMD : M ≤ normalizer (D : Set G)) (hND : N ≤ normalizer (D : Set G))
    (hNM : N ≤ centralizer (M : Set G)) (hDM : ⁅D, M⁆ ≤ R) (hRM : R ⊓ M = ⊥)
    (hZ : (center ↥M).map M.subtype ≤ D) : (D ⊔ M) ⊓ (D ⊔ N) ≤ D := by
  intro x hx
  obtain ⟨hxM, hxN⟩ := hx
  change x ∈ (↑(D ⊔ M) : Set G) at hxM
  rw [coe_mul_of_right_le_normalizer_left D M hMD, Set.mem_mul] at hxM
  obtain ⟨d, hd, m, hm, rfl⟩ := hxM
  change d * m ∈ (↑(D ⊔ N) : Set G) at hxN
  rw [coe_mul_of_right_le_normalizer_left D N hND, Set.mem_mul] at hxN
  obtain ⟨d', hd', n, hn, h_eq⟩ := hxN
  have he : d⁻¹ * d' ∈ D := D.mul_mem (D.inv_mem hd) hd'
  have hm_eq : m = d⁻¹ * d' * n := by
    rw [show m = d⁻¹ * (d * m) by group, ← h_eq]
    group
  have hmD : m ∈ D := by
    apply hZ
    rw [Subgroup.mem_map]
    refine ⟨⟨m, hm⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro m'
    apply Subtype.ext
    show (m' : G) * m = m * (m' : G)
    have hn_comm : n * (m' : G) = (m' : G) * n :=
      (Subgroup.mem_centralizer_iff.mp (hNM hn) (m' : G) m'.2).symm
    have hstep : ⁅d⁻¹ * d' * n, (m' : G)⁆
        = (d⁻¹ * d') * ⁅n, (m' : G)⁆ * (d⁻¹ * d')⁻¹ * ⁅d⁻¹ * d', (m' : G)⁆ := by
      simp only [commutatorElement_def]
      group
    have hcm : ⁅m, (m' : G)⁆ = ⁅d⁻¹ * d', (m' : G)⁆ := by
      rw [hm_eq, hstep, commutatorElement_eq_one_iff_mul_comm.mpr hn_comm]
      group
    have hMem : ⁅m, (m' : G)⁆ ∈ M := by
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm m'.2) (M.inv_mem hm)) (M.inv_mem m'.2)
    have hR : ⁅m, (m' : G)⁆ ∈ R := by
      rw [hcm]
      exact hDM (commutator_mem_commutator he m'.2)
    have h1 : ⁅m, (m' : G)⁆ = 1 := by
      have hmem : ⁅m, (m' : G)⁆ ∈ R ⊓ M := ⟨hR, hMem⟩
      rw [hRM] at hmem
      simpa using hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  exact D.mul_mem hd hmD

end CFSG.GroupTheory
