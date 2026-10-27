module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.CGT.PushingUpLit.SolK.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_commutator (g a b : G) : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutator_mul_left' (a b c : G) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_commutator_mul (x y : G) : x * y * x⁻¹ = ⁅x, y⁆ * y := by
  simp only [commutatorElement_def]
  group

theorem commutator_inv' (x y : G) : ⁅x, y⁆⁻¹ = ⁅y, x⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutator_eq_one_of_comm {a b : G} (h : a * b = b * a) : ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def, h]
  group

theorem comm_of_conj_eq {a b : G} (h : a * b * a⁻¹ = b) : a * b = b * a :=
  mul_inv_eq_iff_eq_mul.1 h

abbrev rOf (M X : Subgroup G) : Subgroup G := pCoreOf 2 M ⊓ Subgroup.centralizer (X : Set G)

theorem pCoreOf_le_self (H : Subgroup G) : pCoreOf 2 H ≤ H := CFSG.openPCoreOf_le 2 H

theorem isPGroup_pCoreOf' (H : Subgroup G) : IsPGroup 2 (pCoreOf 2 H) := by
  rw [pCoreOf_eq_map]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype

theorem le_pCoreOf' {N H : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hp : IsPGroup 2 N) : N ≤ pCoreOf 2 H :=
  CFSG.LieType.BorelTits.le_pCoreOf 2 hNH hN hp

theorem le_pCoreOf_of_normalized {N H : Subgroup G} (hNH : N ≤ H)
    (hnorm : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) (hp : IsPGroup 2 N) : N ≤ pCoreOf 2 H := by
  refine le_pCoreOf' hNH ⟨fun x hx h => ?_⟩ hp
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have := hnorm h h.2 x hx
  simpa using this

theorem pCoreOf_normalized (H : Subgroup G) {h : G} (hh : h ∈ H) {x : G} (hx : x ∈ pCoreOf 2 H) :
    h * x * h⁻¹ ∈ pCoreOf 2 H := by
  have h1 : h ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hh
  have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := H) (CFSG.pCore 2 ↥H) h1
  rw [← pCoreOf_eq_map] at h2
  exact (Subgroup.mem_normalizer_iff.1 h2 x).1 hx


end CFSG.CGT.PushingUpLit.SolK
