module

public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

structure FzSuz (S : Type) [Group S] : Prop where
  card : Nat.card S = 64
  comm_central : ∀ g h : S, ⁅g, h⁆ ∈ center S
  sq_central : ∀ g : S, g * g ∈ center S
  center_card : Nat.card (center S) = 4
  center_exp : ∀ z ∈ center S, z * z = 1
  aniso : ∀ g : S, g * g = 1 → g ∈ center S

theorem FzSuz.of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (h : FzSuz S') :
    FzSuz S := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨(Nat.card_congr e.toEquiv).trans h1, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h
    rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    simp only [map_mul, map_commutatorElement]
    exact Subgroup.mem_center_iff.mp (h2 (e g) (e h)) (e x)
  · intro g
    rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    simp only [map_mul]
    exact Subgroup.mem_center_iff.mp (h3 (e g)) (e x)
  · refine (Nat.card_congr (e.toEquiv.subtypeEquiv (fun z => ?_))).trans h4
    simp only [Subgroup.mem_center_iff]
    constructor
    · intro hz x'
      obtain ⟨x, rfl⟩ := e.surjective x'
      show e x * e z = e z * e x
      rw [← map_mul, ← map_mul, hz x]
    · intro hz x
      apply e.injective
      simp only [map_mul]
      exact hz (e x)
  · intro z hz
    have hz' : e z ∈ center S' := by
      rw [Subgroup.mem_center_iff]
      intro x'
      obtain ⟨x, rfl⟩ := e.surjective x'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    apply e.injective
    rw [map_mul, map_one]
    exact h5 (e z) hz'
  · intro g hg
    rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    simp only [map_mul]
    have hg' : e g * e g = 1 := by rw [← map_mul, hg, map_one]
    have hmem := h6 (e g) hg'
    rw [Subgroup.mem_center_iff] at hmem
    exact hmem (e x)

variable {S : Type} [Group S]

private theorem fzl_conj_center {z : S} (hz : z ∈ center S) (g : S) : g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.mp hz g]
  group

private theorem fzl_center_inv_aux (hS : FzSuz S) {z : S} (hz : z ∈ center S) : z⁻¹ = z :=
  mul_eq_one_iff_inv_eq.mp (hS.center_exp z hz)

theorem fzl_gam_mul_left (hS : FzSuz S) (g g' h : S) : ⁅g * g', h⁆ = ⁅g, h⁆ * ⁅g', h⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, fzl_conj_center (hS.comm_central g' h) g]
  exact (Subgroup.mem_center_iff.mp (hS.comm_central g' h) ⁅g, h⁆).symm

theorem fzl_gam_mul_right (hS : FzSuz S) (g h h' : S) : ⁅g, h * h'⁆ = ⁅g, h⁆ * ⁅g, h'⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  rw [show ⁅g, h⁆ * h * ⁅g, h'⁆ * h⁻¹ = ⁅g, h⁆ * (h * ⁅g, h'⁆ * h⁻¹) by group]
  rw [fzl_conj_center (hS.comm_central g h') h]

theorem fzl_gam_symm (hS : FzSuz S) (g h : S) : ⁅g, h⁆ = ⁅h, g⁆ := by
  rw [← commutatorElement_inv]
  exact fzl_center_inv_aux hS (hS.comm_central h g)

theorem fzl_gam_inv_right (hS : FzSuz S) (g h : S) : ⁅g, h⁻¹⁆ = ⁅g, h⁆ := by
  have h1 := fzl_gam_mul_right hS g h h⁻¹
  rw [mul_inv_cancel, commutatorElement_one_right] at h1
  have h2 : (⁅g, h⁆)⁻¹ = ⁅g, h⁻¹⁆ := mul_eq_one_iff_inv_eq.mp h1.symm
  rw [fzl_center_inv_aux hS (hS.comm_central g h)] at h2
  exact h2.symm

theorem fzl_gam_mul_central (hS : FzSuz S) {z : S} (hz : z ∈ center S) (g h : S) :
    ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hz' : ⁅z, h⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz h).symm
  rw [fzl_gam_mul_left hS g z h, hz', mul_one]

theorem fzl_gam_self (g : S) : ⁅g, g⁆ = 1 :=
  commutatorElement_self g

theorem fzl_sq_mul (hS : FzSuz S) (g h : S) :
    (g * h) * (g * h) = (g * g) * (h * h) * ⁅g, h⁆ := by
  have hs : ⁅h, g⁆ ∈ center S := hS.comm_central h g
  have key : h * g = ⁅h, g⁆ * g * h := by
    rw [commutatorElement_def h g]
    group
  calc (g * h) * (g * h) = g * (h * g) * h := by group
    _ = g * (⁅h, g⁆ * g * h) * h := congrArg (fun x => g * x * h) key
    _ = g * ⁅h, g⁆ * g * h * h := by group
    _ = ⁅h, g⁆ * ((g * g) * (h * h)) := by
          rw [Subgroup.mem_center_iff.mp hs g]; group
    _ = ⁅g, h⁆ * ((g * g) * (h * h)) :=
          congrArg (fun x => x * ((g * g) * (h * h))) (fzl_gam_symm hS h g)
    _ = (g * g) * (h * h) * ⁅g, h⁆ :=
          (Subgroup.mem_center_iff.mp (hS.comm_central g h) ((g * g) * (h * h))).symm

theorem fzl_sq_mul_central (hS : FzSuz S) {z : S} (hz : z ∈ center S) (g : S) :
    (g * z) * (g * z) = g * g := by
  have hzg : z * g = g * z := (Subgroup.mem_center_iff.mp hz g).symm
  calc (g * z) * (g * z) = g * (z * g) * z := by group
    _ = g * (g * z) * z := congrArg (fun x => g * x * z) hzg
    _ = (g * g) * (z * z) := by group
    _ = (g * g) * 1 := congrArg (fun x => (g * g) * x) (hS.center_exp z hz)
    _ = g * g := mul_one (g * g)

theorem fzl_map_center (α : MulAut S) {z : S} (hz : z ∈ center S) : α z ∈ center S := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨y, rfl⟩ := α.surjective x
  simp only [← map_mul, Subgroup.mem_center_iff.mp hz y]

theorem fzl_center_inv (hS : FzSuz S) {z : S} (hz : z ∈ center S) : z⁻¹ = z :=
  fzl_center_inv_aux hS hz

end CFSG.OddStandard.SmallF3.FritzII
